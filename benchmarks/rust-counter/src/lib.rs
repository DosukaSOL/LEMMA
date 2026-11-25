#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(always)]
unsafe fn next_cursor(acc: *const u8) -> *const u8 {
    if *acc == 0xFF {
        let dlen = *(acc.add(80) as *const u64) as usize;
        let stride = (dlen + 10343) & !7usize;
        acc.add(stride)
    } else {
        acc.add(8)
    }
}

/// Hand-rolled zero-dep `#![no_std]` Rust equivalent of `Examples.Counter.entrypoint`.
#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let n = *(input as *const u64);
    if n < 1 {
        return 0x0000000b00000000;
    }
    let acc = input.add(8);
    let mut cur = next_cursor(acc);
    let mut rem = n - 1;
    while rem != 0 {
        cur = next_cursor(cur);
        rem -= 1;
    }
    let ix_len = *(cur as *const u64);
    let ix_ptr = cur.add(8);

    if *acc.add(2) == 0 {
        return 0x0000000400000000; // invalidAccountData
    }
    let dlen = *(acc.add(80) as *const u64);
    if dlen < 8 {
        return 0x0000000500000000; // accountDataTooSmall
    }
    if ix_len < 1 {
        return 0x0000000300000000; // invalidInstructionData
    }
    let op = *ix_ptr;
    let count_ptr = acc.add(88) as *mut u64;
    match op {
        0 => {
            *count_ptr = 0;
            0
        }
        1 => {
            let cur_val = *count_ptr;
            match cur_val.checked_add(1) {
                Some(next) => {
                    *count_ptr = next;
                    0
                }
                None => 0x0000001800000000,
            }
        }
        2 => {
            if ix_len < 9 {
                return 0x0000000300000000;
            }
            let delta = core::ptr::read_unaligned(ix_ptr.add(1) as *const u64);
            let cur_val = *count_ptr;
            match cur_val.checked_add(delta) {
                Some(next) => {
                    *count_ptr = next;
                    0
                }
                None => 0x0000001800000000,
            }
        }
        3 => {
            if *acc.add(1) == 0 {
                return 0x0000000800000000; // missingRequiredSignature
            }
            *count_ptr = 0;
            0
        }
        _ => 0x0000000300000000,
    }
}
