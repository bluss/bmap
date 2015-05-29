use std::mem;

enum Void { }

/// FIXME: Replace with intrinsic when it's stable
#[inline]
pub unsafe fn unreachable() -> ! {
    let void: &Void = mem::transmute(&());
    match *void {
        // no cases
    }
}

#[inline]
pub unsafe fn debug_assert_unreachable() -> ! {
    debug_assert!(false, "Entered unreachable section, this is a bug!");
    unreachable()
}

