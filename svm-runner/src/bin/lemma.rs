//! LEMMA on the real SVM: replays `vectors/*.json` against the compiled probe programs and runs
//! the GuardedCounter attack scenarios, all in LiteSVM (Agave). Uses only the crates already in
//! upstream's `svm-runner/Cargo.lock` (no new dependencies).
//!
//! Run: `scripts/build-programs.sh && cargo run --locked --release --manifest-path svm-runner/Cargo.toml --bin lemma`

use {
    litesvm::LiteSVM,
    solana_account::Account,
    solana_address::Address,
    solana_instruction::{account_meta::AccountMeta, Instruction},
    solana_keypair::Keypair,
    solana_message::Message,
    solana_signer::Signer,
    solana_transaction::Transaction,
    std::path::PathBuf,
};

const ERR_MISMATCH: &str = "Custom(2989)"; // 0xBAD
const ERR_DIV_ZERO: &str = "Custom(1280114689)"; // 0x4C4D0001
const ERR_DUPLICATE: &str = "Custom(1280114690)"; // 0x4C4D0002
const ERR_WRONG_KIND: &str = "Custom(1280114691)"; // 0x4C4D0003
const COUNTER_TAG: u64 = 0x52544E554F434D4C;

fn repo_path(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join(rel)
}

fn load_so(name: &str) -> Vec<u8> {
    let p = repo_path(&format!("build/{name}"));
    std::fs::read(&p).unwrap_or_else(|e| panic!("failed to read {}: {e}", p.display()))
}

struct Ctx {
    svm: LiteSVM,
    payer: Keypair,
    nonce: u64,
}

impl Ctx {
    fn new() -> Self {
        let mut svm = LiteSVM::new();
        let payer = Keypair::new();
        svm.airdrop(&payer.pubkey(), 100_000_000_000).unwrap();
        Ctx { svm, payer, nonce: 0 }
    }

    /// Send one instruction; a nonce is appended to the data so repeated inputs are distinct
    /// transactions. Returns `Ok(())` or the Debug rendering of the failure.
    fn send(&mut self, program_id: Address, accounts: Vec<AccountMeta>, mut data: Vec<u8>,
            signers: &[&Keypair]) -> Result<u64, String> {
        self.nonce += 1;
        data.extend_from_slice(&self.nonce.to_le_bytes());
        let ix = Instruction { program_id, accounts, data };
        let blockhash = self.svm.latest_blockhash();
        let msg = Message::new(&[ix], Some(&self.payer.pubkey()));
        let mut all: Vec<&Keypair> = vec![&self.payer];
        all.extend_from_slice(signers);
        let tx = Transaction::new(&all, msg, blockhash);
        match self.svm.send_transaction(tx) {
            Ok(meta) => Ok(meta.compute_units_consumed),
            Err(e) => Err(format!("{e:?}")),
        }
    }
}

/// Value of `"key": "…"` on a single JSON line of a vectors file.
fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("\"{key}\": \"");
    let start = line.find(&pat)? + pat.len();
    let end = line[start..].find('"')? + start;
    Some(&line[start..end])
}

fn u64f(line: &str, key: &str) -> u64 {
    field(line, key).unwrap_or_else(|| panic!("missing {key} in {line}")).parse().unwrap()
}

fn error_substring(kind: &str) -> &'static str {
    match kind {
        "divByZero" => ERR_DIV_ZERO,
        "overflow" => "ArithmeticOverflow",
        "invalidArgument" => "InvalidArgument",
        other => panic!("unknown error kind {other}"),
    }
}

/// Replay one vectors file. `encode` builds instruction data (without the trailing `c`).
fn replay(ctx: &mut Ctx, program_id: Address, file: &str, key0: &str,
          encode: &dyn Fn(&str) -> Vec<u8>) -> (usize, u64) {
    let text = std::fs::read_to_string(repo_path(file)).expect("vectors file");
    let mut n = 0;
    let mut max_cu = 0;
    for line in text.lines().filter(|l| l.contains(&format!("\"{key0}\": "))) {
        let base = encode(line);
        match field(line, "expected") {
            Some(v) => {
                let v: u64 = v.parse().unwrap();
                let mut ok = base.clone();
                ok.extend_from_slice(&v.to_le_bytes());
                match ctx.send(program_id, vec![], ok, &[]) {
                    Ok(cu) => max_cu = max_cu.max(cu),
                    Err(e) => panic!("{file}: expected {v} but failed: {e}\n  case: {line}"),
                }
                let mut bad = base;
                bad.extend_from_slice(&v.wrapping_add(1).to_le_bytes());
                let r = ctx.send(program_id, vec![], bad, &[]);
                assert!(matches!(&r, Err(e) if e.contains(ERR_MISMATCH)),
                        "{file}: wrong value not rejected: {r:?}\n  case: {line}");
            }
            None => {
                let want = error_substring(field(line, "error").expect("error kind"));
                let mut d = base;
                d.extend_from_slice(&0u64.to_le_bytes());
                let r = ctx.send(program_id, vec![], d, &[]);
                assert!(matches!(&r, Err(e) if e.contains(want)),
                        "{file}: expected error {want}, got {r:?}\n  case: {line}");
            }
        }
        n += 1;
    }
    (n, max_cu)
}

fn vectors() {
    let mut ctx = Ctx::new();
    let md = Address::new_unique();
    ctx.svm.add_program(md, &load_so("probe_muldiv.so")).unwrap();
    let sw = Address::new_unique();
    ctx.svm.add_program(sw, &load_so("probe_swap.so")).unwrap();

    for (file, mode) in [("vectors/mulDivFloor.json", 0u8), ("vectors/mulDivCeil.json", 1u8)] {
        let (n, cu) = replay(&mut ctx, md, file, "a", &|l| {
            let mut d = Vec::new();
            for k in ["a", "b", "d"] { d.extend_from_slice(&u64f(l, k).to_le_bytes()); }
            d.push(mode);
            d
        });
        println!("[PASS] {file:<26} {n:>5} vectors on LiteSVM (max {cu} CU)");
    }
    let (n, cu) = replay(&mut ctx, sw, "vectors/swapOut.json", "reserveIn", &|l| {
        let mut d = Vec::new();
        for k in ["reserveIn", "reserveOut", "amountIn", "feeBps"] {
            d.extend_from_slice(&u64f(l, k).to_le_bytes());
        }
        d
    });
    println!("[PASS] vectors/swapOut.json       {n:>5} vectors on LiteSVM (max {cu} CU)");
}

/// LEMMA patch 0001 on the real VM: exact `Nat` addition, abort on overflow.
fn nat_abort() {
    let mut ctx = Ctx::new();
    let p = Address::new_unique();
    ctx.svm.add_program(p, &load_so("probe_nat_add.so")).unwrap();
    let enc = |a: u64, b: u64, c: u64| {
        let mut d = Vec::new();
        for x in [a, b, c] { d.extend_from_slice(&x.to_le_bytes()); }
        d
    };
    ctx.send(p, vec![], enc(40, 2, 42), &[]).expect("exact Nat add must succeed");
    let r = ctx.send(p, vec![], enc(40, 2, 43), &[]);
    assert!(matches!(&r, Err(e) if e.contains(ERR_MISMATCH)), "wrong sum accepted: {r:?}");
    // 2^64 - 1 + 2 overflows 64 bits: Lean says the sum is 2^64 + 1 (≠ any u64), the patched
    // binary must abort rather than wrap to 1.
    let r = ctx.send(p, vec![], enc(u64::MAX, 2, 1), &[]);
    match &r {
        Err(e) if !e.contains("Custom(") => println!("[PASS] Nat overflow aborts on the real VM: {e}"),
        other => panic!("Nat overflow must abort (not wrap/succeed or return a custom code): {other:?}"),
    }
}

fn guarded_counter() {
    let so = load_so("guarded_counter.so");
    let mut ctx = Ctx::new();
    let program_id = Address::new_unique();
    ctx.svm.add_program(program_id, &so).unwrap();
    let auth = Keypair::new();
    let other = Keypair::new();

    let make_counter = |ctx: &mut Ctx, owner: Address, tag: u64, count: u64| -> Address {
        let addr = Address::new_unique();
        let mut data = tag.to_le_bytes().to_vec();
        data.extend_from_slice(&auth.pubkey().to_bytes());
        data.extend_from_slice(&count.to_le_bytes());
        ctx.svm.set_account(addr, Account {
            lamports: 10_000_000, data, owner, ..Default::default()
        }).unwrap();
        addr
    };
    let count_of = |ctx: &Ctx, a: &Address| -> u64 {
        u64::from_le_bytes(ctx.svm.get_account(a).unwrap().data[40..48].try_into().unwrap())
    };
    let expect_err = |r: Result<u64, String>, want: &str, name: &str| match r {
        Err(e) if e.contains(want) => println!("[PASS] GuardedCounter rejects: {name}"),
        other => panic!("GuardedCounter / {name}: expected {want}, got {other:?}"),
    };

    let c = make_counter(&mut ctx, program_id, COUNTER_TAG, 41);
    let cu = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true), AccountMeta::new(c, false)],
                      vec![], &[&auth]).expect("honest increment");
    assert_eq!(count_of(&ctx, &c), 42);
    println!("[PASS] GuardedCounter honest increment 41 -> 42 ({cu} CU, {} B .so)", so.len());

    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), false), AccountMeta::new(c, false)], vec![], &[]);
    expect_err(r, "MissingRequiredSignature", "missing signer");
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true), AccountMeta::new_readonly(c, false)], vec![], &[&auth]);
    expect_err(r, "InvalidAccountData", "counter passed read-only");
    let spoof = make_counter(&mut ctx, Address::new_unique(), COUNTER_TAG, 41);
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true), AccountMeta::new(spoof, false)], vec![], &[&auth]);
    expect_err(r, "IllegalOwner", "counter owned by another program");
    let wrong = make_counter(&mut ctx, program_id, COUNTER_TAG + 1, 41);
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true), AccountMeta::new(wrong, false)], vec![], &[&auth]);
    expect_err(r, ERR_WRONG_KIND, "wrong account kind (type confusion)");
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(other.pubkey(), true), AccountMeta::new(c, false)], vec![], &[&other]);
    expect_err(r, "IllegalOwner", "signer is not the stored authority");
    let r = ctx.send(program_id, vec![AccountMeta::new(auth.pubkey(), true), AccountMeta::new(auth.pubkey(), true)], vec![], &[&auth]);
    expect_err(r, ERR_DUPLICATE, "authority passed twice (duplicate slot)");
    let full = make_counter(&mut ctx, program_id, COUNTER_TAG, u64::MAX);
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true), AccountMeta::new(full, false)], vec![], &[&auth]);
    expect_err(r, "ArithmeticOverflow", "counter overflow");
    assert_eq!(count_of(&ctx, &full), u64::MAX);
    let r = ctx.send(program_id, vec![AccountMeta::new_readonly(auth.pubkey(), true)], vec![], &[&auth]);
    expect_err(r, "NotEnoughAccountKeys", "too few accounts");
    assert_eq!(count_of(&ctx, &c), 42, "failed attacks must not change the counter");
}

fn main() {
    println!("== LEMMA on LiteSVM ==");
    guarded_counter();
    nat_abort();
    vectors();
    println!("== ALL LEMMA LITESVM CHECKS PASSED ==");
}
