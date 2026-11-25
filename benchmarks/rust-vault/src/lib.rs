#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn sol_log_(ptr: *const u8, len: u64);
}

#[inline(always)]
unsafe fn next_cursor(acc: *const u8) -> *const u8 {
    if *acc == 0xFF {
        let dlen = *(acc.add(80) as *const u64) as usize;
        acc.add((dlen + 10343) & !7usize)
    } else {
        acc.add(8)
    }
}

#[inline(always)]
unsafe fn pubkey_eq(a: *const u8, b: *const u8) -> bool {
    *(a as *const u64) == *(b as *const u64)
        && *(a.add(8) as *const u64) == *(b.add(8) as *const u64)
        && *(a.add(16) as *const u64) == *(b.add(16) as *const u64)
        && *(a.add(24) as *const u64) == *(b.add(24) as *const u64)
}

/// Hand-rolled zero-dep `#![no_std]` Rust equivalent of `Examples.Vault.entrypoint`.
#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let n = *(input as *const u64);
    if n < 3 {
        return 0x0000000b00000000;
    }
    let auth = input.add(8);
    let from_vault = next_cursor(auth) as *mut u8;
    let to_dest = next_cursor(from_vault) as *mut u8;
    let mut cur = next_cursor(to_dest);
    let mut rem = n - 3;
    while rem != 0 {
        cur = next_cursor(cur);
        rem -= 1;
    }
    let ix_len = *(cur as *const u64);
    let ix_ptr = cur.add(8);

    if *auth.add(1) == 0 {
        return 0x0000000800000000;
    }
    if *from_vault.add(2) == 0 || *to_dest.add(2) == 0 {
        return 0x0000000400000000;
    }
    if *(from_vault.add(80) as *const u64) < 32 {
        return 0x0000000500000000;
    }
    if !pubkey_eq(from_vault.add(88), auth.add(8)) {
        return 0x0000001200000000;
    }
    if ix_len < 8 {
        return 0x0000000300000000;
    }
    let amount = core::ptr::read_unaligned(ix_ptr as *const u64);
    let from_bal = *(from_vault.add(72) as *const u64);
    let new_from = match from_bal.checked_sub(amount) {
        Some(v) => v,
        None => return 0x0000000600000000,
    };
    let to_bal = *(to_dest.add(72) as *const u64);
    let new_to = match to_bal.checked_add(amount) {
        Some(v) => v,
        None => return 0x0000001800000000,
    };
    *(from_vault.add(72) as *mut u64) = new_from;
    *(to_dest.add(72) as *mut u64) = new_to;
    let msg = b"lean-svm: vault transfer ok";
    sol_log_(msg.as_ptr(), msg.len() as u64);
    0
}
