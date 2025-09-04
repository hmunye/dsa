#[allow(unused_macros)]
macro_rules! do_while {
    (
        init {
            $($s:stmt;)*
        }
        do $do:block
        while $cond:expr
    ) => {{
        $($s)*

        loop {
            $do
            if !$cond {
                break;
            }
        }
    }};
}

fn main() {
    let mut arr = [0u8; 6];
    let ptr: *mut _ = arr.as_mut_ptr();

    println!("ptr: {ptr:p}\tarr: {arr:02x?}\tlen: {}", arr.len());

    unsafe {
        *ptr.wrapping_add(0) = 45;
        println!("ptr: {ptr:p}\tarr: {arr:02x?}\tlen: {}", arr.len());

        *ptr.wrapping_add(2) = 45;
        println!("ptr: {ptr:p}\tarr: {arr:02x?}\tlen: {}", arr.len());

        let ptr = ptr as *mut u16;
        *ptr.wrapping_add(2) = 0x4545;
        println!("ptr: {ptr:p}\tarr: {arr:02x?}\tlen: {}", arr.len());

        *ptr.wrapping_add(2) = 0x45;
        println!("ptr: {ptr:p}\tarr: {arr:02x?}\tlen: {}", arr.len());
    }
}
