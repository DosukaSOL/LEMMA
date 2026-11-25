#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[repr(C)]
struct SolInstruction {
    program_id_addr: u64,
    accounts_addr: u64,
    accounts_len: u64,
    data_addr: u64,
    data_len: u64,
}

#[repr(C)]
struct SolAccountMeta {
    pubkey_addr: u64,
    is_writable: bool,
    is_signer: bool,
}

#[repr(C)]
struct SolAccountInfo {
    key_addr: u64,
    lamports_addr: u64,
    data_len: u64,
    data_addr: u64,
    owner_addr: u64,
    rent_epoch: u64,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
}

#[repr(C)]
struct SolSignerSeed {
    addr: u64,
    len: u64,
}

#[repr(C)]
struct SolSignerSeeds {
    addr: u64,
    len: u64,
}

extern "C" {
    fn sol_get_clock_sysvar(out: *mut u8) -> u64;
    fn sol_invoke_signed_c(
        ix: *const SolInstruction,
        infos: *const SolAccountInfo,
        infos_len: u64,
        signers: *const SolSignerSeeds,
        signers_len: u64,
    ) -> u64;
}

#[inline(never)]
unsafe fn next_cursor(acc: *const u8) -> *const u8 {
    if *acc == 0xFF {
        let dlen = *(acc.add(80) as *const u64) as usize;
        acc.add((dlen + 10343) & !7usize)
    } else {
        acc.add(8)
    }
}

#[inline(never)]
unsafe fn pubkey_eq(a: *const u8, b: *const u8) -> bool {
    *(a as *const u64) == *(b as *const u64)
        && *(a.add(8) as *const u64) == *(b.add(8) as *const u64)
        && *(a.add(16) as *const u64) == *(b.add(16) as *const u64)
        && *(a.add(24) as *const u64) == *(b.add(24) as *const u64)
}

#[inline(never)]
unsafe fn pubkey_copy(dst: *mut u8, src: *const u8) {
    *(dst as *mut u64) = *(src as *const u64);
    *(dst.add(8) as *mut u64) = *(src.add(8) as *const u64);
    *(dst.add(16) as *mut u64) = *(src.add(16) as *const u64);
    *(dst.add(24) as *mut u64) = *(src.add(24) as *const u64);
}

#[inline(always)]
unsafe fn mk_info(acc: *const u8) -> SolAccountInfo {
    SolAccountInfo {
        key_addr: acc.add(8) as u64,
        lamports_addr: acc.add(72) as u64,
        data_len: *(acc.add(80) as *const u64),
        data_addr: acc.add(88) as u64,
        owner_addr: acc.add(40) as u64,
        rent_epoch: 0,
        is_signer: *acc.add(1) != 0,
        is_writable: *acc.add(2) != 0,
        executable: *acc.add(3) != 0,
    }
}

#[inline(never)]
unsafe fn cpi_transfer_checked(
    tok_prog: *const u8,
    src: *const u8,
    mint: *const u8,
    dst: *const u8,
    auth: *const u8,
    amount: u64,
    decimals: u8,
    signers: *const SolSignerSeeds,
    signers_len: u64,
) -> u64 {
    let mut data = [0u8; 10];
    data[0] = 12;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    data[9] = decimals;
    let metas = [
        SolAccountMeta { pubkey_addr: src.add(8) as u64, is_writable: true, is_signer: false },
        SolAccountMeta { pubkey_addr: mint.add(8) as u64, is_writable: false, is_signer: false },
        SolAccountMeta { pubkey_addr: dst.add(8) as u64, is_writable: true, is_signer: false },
        SolAccountMeta { pubkey_addr: auth.add(8) as u64, is_writable: false, is_signer: true },
    ];
    let infos = [mk_info(src), mk_info(mint), mk_info(dst), mk_info(auth)];
    let ix = SolInstruction {
        program_id_addr: tok_prog.add(8) as u64,
        accounts_addr: metas.as_ptr() as u64,
        accounts_len: 4,
        data_addr: data.as_ptr() as u64,
        data_len: 10,
    };
    sol_invoke_signed_c(&ix, infos.as_ptr(), 4, signers, signers_len)
}

#[inline(never)]
unsafe fn cpi_system_transfer(
    sys_prog: *const u8,
    from: *const u8,
    to: *const u8,
    lamports: u64,
) -> u64 {
    let mut data = [0u8; 12];
    data[0..4].copy_from_slice(&2u32.to_le_bytes());
    data[4..12].copy_from_slice(&lamports.to_le_bytes());
    let metas = [
        SolAccountMeta { pubkey_addr: from.add(8) as u64, is_writable: true, is_signer: true },
        SolAccountMeta { pubkey_addr: to.add(8) as u64, is_writable: true, is_signer: false },
    ];
    let infos = [mk_info(from), mk_info(to)];
    let ix = SolInstruction {
        program_id_addr: sys_prog.add(8) as u64,
        accounts_addr: metas.as_ptr() as u64,
        accounts_len: 2,
        data_addr: data.as_ptr() as u64,
        data_len: 12,
    };
    sol_invoke_signed_c(&ix, infos.as_ptr(), 2, core::ptr::null(), 0)
}

/// Hand-rolled zero-dep `#![no_std]` Rust equivalent of `Examples.DutchAuction.entrypoint`.
#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let n = *(input as *const u64);
    let a0 = input.add(8);
    let mut cur = a0 as *const u8;
    let mut rem = n;
    while rem != 0 {
        cur = next_cursor(cur);
        rem -= 1;
    }
    let ix_len = *(cur as *const u64);
    let ix_ptr = cur.add(8);
    if ix_len < 1 {
        return 0x0000000300000000;
    }
    match *ix_ptr {
        0 => {
            if n < 6 || ix_len < 35 { return 0x0000000300000000; }
            let seller = a0 as *const u8;
            let auction = next_cursor(seller) as *mut u8;
            let nft_mint = next_cursor(auction);
            let seller_nft = next_cursor(nft_mint);
            let escrow = next_cursor(seller_nft);
            let tok_prog = next_cursor(escrow);
            if *seller.add(1) == 0 { return 0x0000000800000000; }
            if *auction.add(2) == 0 { return 0x0000000400000000; }
            if *(auction.add(80) as *const u64) < 144 { return 0x0000000500000000; }
            let ad = auction.add(88);
            if *ad != 0 { return 0x0000000900000000; }
            let bump = *ix_ptr.add(1);
            let dec = *ix_ptr.add(2);
            let start_p = core::ptr::read_unaligned(ix_ptr.add(3) as *const u64);
            let reserve_p = core::ptr::read_unaligned(ix_ptr.add(11) as *const u64);
            let start_s = core::ptr::read_unaligned(ix_ptr.add(19) as *const u64);
            let end_s = core::ptr::read_unaligned(ix_ptr.add(27) as *const u64);
            if start_p < reserve_p || end_s <= start_s { return 0x0000000200000000; }
            let rc = cpi_transfer_checked(tok_prog, seller_nft, nft_mint, escrow, seller, 1, dec, core::ptr::null(), 0);
            if rc != 0 { return rc; }
            *ad = 1;
            *ad.add(1) = bump;
            *ad.add(2) = dec;
            pubkey_copy(ad.add(8), seller.add(8));
            pubkey_copy(ad.add(40), nft_mint.add(8));
            pubkey_copy(ad.add(72), escrow.add(8));
            *(ad.add(104) as *mut u64) = start_p;
            *(ad.add(112) as *mut u64) = reserve_p;
            *(ad.add(120) as *mut u64) = start_s;
            *(ad.add(128) as *mut u64) = end_s;
            *(ad.add(136) as *mut u64) = 0;
            0
        }
        1 => {
            if n < 9 || ix_len < 9 { return 0x0000000300000000; }
            let buyer = a0 as *const u8;
            let seller = next_cursor(buyer);
            let auction = next_cursor(seller) as *mut u8;
            let pda_auth = next_cursor(auction);
            let nft_mint = next_cursor(pda_auth);
            let escrow = next_cursor(nft_mint);
            let buyer_nft = next_cursor(escrow);
            let tok_prog = next_cursor(buyer_nft);
            let sys_prog = next_cursor(tok_prog);
            if *buyer.add(1) == 0 { return 0x0000000800000000; }
            if *auction.add(2) == 0 { return 0x0000000400000000; }
            let ad = auction.add(88);
            if *ad != 1 { return 0x0000000400000000; }
            if !pubkey_eq(ad.add(8), seller.add(8)) { return 0x0000001200000000; }
            if !pubkey_eq(ad.add(40), nft_mint.add(8)) { return 0x0000000400000000; }
            if !pubkey_eq(ad.add(72), escrow.add(8)) { return 0x0000000400000000; }
            let max_p = core::ptr::read_unaligned(ix_ptr.add(1) as *const u64);
            let start_p = *(ad.add(104) as *const u64);
            let reserve_p = *(ad.add(112) as *const u64);
            let start_s = *(ad.add(120) as *const u64);
            let end_s = *(ad.add(128) as *const u64);
            let mut clk = [0u8; 40];
            if sol_get_clock_sysvar(clk.as_mut_ptr()) != 0 { return 0x0000001100000000; }
            let cur_s = *(clk.as_ptr() as *const u64);
            let price = if cur_s <= start_s {
                start_p
            } else if cur_s >= end_s {
                reserve_p
            } else {
                let drop = (((start_p - reserve_p) as u128 * (cur_s - start_s) as u128)
                    / (end_s - start_s) as u128) as u64;
                start_p - drop
            };
            if price > max_p { return 0x0000000200000000; }
            let rc1 = cpi_system_transfer(sys_prog, buyer, seller, price);
            if rc1 != 0 { return rc1; }
            let bump = [*ad.add(1)];
            let dec = *ad.add(2);
            let tag = *b"auct";
            let seeds = [
                SolSignerSeed { addr: tag.as_ptr() as u64, len: 4 },
                SolSignerSeed { addr: auction.add(8) as u64, len: 32 },
                SolSignerSeed { addr: bump.as_ptr() as u64, len: 1 },
            ];
            let signer = SolSignerSeeds { addr: seeds.as_ptr() as u64, len: 3 };
            let rc2 = cpi_transfer_checked(tok_prog, escrow, nft_mint, buyer_nft, pda_auth, 1, dec, &signer, 1);
            if rc2 != 0 { return rc2; }
            *ad = 2;
            *(ad.add(136) as *mut u64) = price;
            0
        }
        2 => {
            if n < 7 { return 0x0000000b00000000; }
            let seller = a0 as *const u8;
            let auction = next_cursor(seller) as *mut u8;
            let pda_auth = next_cursor(auction);
            let nft_mint = next_cursor(pda_auth);
            let escrow = next_cursor(nft_mint);
            let seller_nft = next_cursor(escrow);
            let tok_prog = next_cursor(seller_nft);
            if *seller.add(1) == 0 { return 0x0000000800000000; }
            if *auction.add(2) == 0 { return 0x0000000400000000; }
            let ad = auction.add(88);
            if *ad != 1 { return 0x0000000400000000; }
            if !pubkey_eq(ad.add(8), seller.add(8)) { return 0x0000001200000000; }
            if !pubkey_eq(ad.add(72), escrow.add(8)) { return 0x0000000400000000; }
            let bump = [*ad.add(1)];
            let dec = *ad.add(2);
            let tag = *b"auct";
            let seeds = [
                SolSignerSeed { addr: tag.as_ptr() as u64, len: 4 },
                SolSignerSeed { addr: auction.add(8) as u64, len: 32 },
                SolSignerSeed { addr: bump.as_ptr() as u64, len: 1 },
            ];
            let signer = SolSignerSeeds { addr: seeds.as_ptr() as u64, len: 3 };
            let rc = cpi_transfer_checked(tok_prog, escrow, nft_mint, seller_nft, pda_auth, 1, dec, &signer, 1);
            if rc != 0 { return rc; }
            *ad = 3;
            0
        }
        _ => 0x0000000300000000,
    }
}
