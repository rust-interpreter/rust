// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// alloc::heap::reallocate test.
//
// Ideally this would be revised to use no_std, but for now it serves
// well enough to reproduce (and illustrate) the bug from #16687.

#![feature(heap_api, allocator_api)]

use std::heap::{Heap, Alloc, Layout};
use std::ptr;

fn main() {
    unsafe {
        assert!(test_triangle());
    }
}

unsafe fn test_triangle() -> bool {
    static COUNT : usize = 16;
    let mut ascend = vec![ptr::null_mut(); COUNT];
    let ascend = &mut *ascend;
    static ALIGN : usize = 1;

    // Checks that `ascend` forms triangle of ascending size formed
    // from pairs of rows (where each pair of rows is equally sized),
    // and the elements of the triangle match their row-pair index.
    unsafe fn sanity_check(ascend: &[*mut u8]) {
        for i in 0..COUNT / 2 {
            let (p0, p1, size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
            for j in 0..size {
                assert_eq!(*p0.offset(j as isize), i as u8);
                assert_eq!(*p1.offset(j as isize), i as u8);
            }
        }
    }

    static PRINT : bool = false;

    unsafe fn allocate(layout: Layout) -> *mut u8 {
        if PRINT {
            println!("allocate({:?})", layout);
        }

        let ret = Heap.alloc(layout.clone()).unwrap_or_else(|_| Heap.oom());

        if PRINT {
            println!("allocate({:?}) = {:?}", layout, ret);
        }

        ret
    }

    unsafe fn deallocate(ptr: *mut u8, layout: Layout) {
        if PRINT {
            println!("deallocate({:?}, {:?}", ptr, layout);
        }

        Heap.dealloc(ptr, layout);
    }

    unsafe fn reallocate(ptr: *mut u8, old: Layout, new: Layout) -> *mut u8 {
        if PRINT {
            println!("reallocate({:?}, old={:?}, new={:?})", ptr, old, new);
        }

        let ret = Heap.realloc(ptr, old.clone(), new.clone())
            .unwrap_or_else(|_| Heap.oom());

        if PRINT {
            println!("reallocate({:?}, old={:?}, new={:?}) = {:?}",
                     ptr, old, new, ret);
        }
        ret
    }

    fn idx_to_size(i: usize) -> usize { (i+1) * 10 }

    // Allocate pairs of rows that form a triangle shape.  (Hope is
    // that at least two rows will be allocated near each other, so
    // that we trigger the bug (a buffer overrun) in an observable
    // way.)
    for i in 0..COUNT / 2 {
        let size = idx_to_size(i);
        ascend[2*i]   = allocate(Layout::from_size_align(size, ALIGN).unwrap());
        ascend[2*i+1] = allocate(Layout::from_size_align(size, ALIGN).unwrap());
    }

    // Initialize each pair of rows to distinct value.
    for i in 0..COUNT / 2 {
        let (p0, p1, size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
        for j in 0..size {
            *p0.offset(j as isize) = i as u8;
            *p1.offset(j as isize) = i as u8;
        }
    }

    sanity_check(&*ascend);
    test_1(ascend); // triangle -> square
    test_2(ascend); // square -> triangle
    test_3(ascend); // triangle -> square
    test_4(ascend); // square -> triangle

    for i in 0..COUNT / 2 {
        let size = idx_to_size(i);
        deallocate(ascend[2*i], Layout::from_size_align(size, ALIGN).unwrap());
        deallocate(ascend[2*i+1], Layout::from_size_align(size, ALIGN).unwrap());
    }

    return true;

    // Test 1: turn the triangle into a square (in terms of
    // allocation; initialized portion remains a triangle) by
    // realloc'ing each row from top to bottom, and checking all the
    // rows as we go.
    unsafe fn test_1(ascend: &mut [*mut u8]) {
        let new_size = idx_to_size(COUNT-1);
        let new = Layout::from_size_align(new_size, ALIGN).unwrap();
        for i in 0..COUNT / 2 {
            let (p0, p1, old_size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
            assert!(old_size < new_size);
            let old = Layout::from_size_align(old_size, ALIGN).unwrap();

            ascend[2*i] = reallocate(p0, old.clone(), new.clone());
            sanity_check(&*ascend);

            ascend[2*i+1] = reallocate(p1, old.clone(), new.clone());
            sanity_check(&*ascend);
        }
    }

    // Test 2: turn the square back into a triangle, top to bottom.
    unsafe fn test_2(ascend: &mut [*mut u8]) {
        let old_size = idx_to_size(COUNT-1);
        let old = Layout::from_size_align(old_size, ALIGN).unwrap();
        for i in 0..COUNT / 2 {
            let (p0, p1, new_size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
            assert!(new_size < old_size);
            let new = Layout::from_size_align(new_size, ALIGN).unwrap();

            ascend[2*i] = reallocate(p0, old.clone(), new.clone());
            sanity_check(&*ascend);

            ascend[2*i+1] = reallocate(p1, old.clone(), new.clone());
            sanity_check(&*ascend);
        }
    }

    // Test 3: turn triangle into a square, bottom to top.
    unsafe fn test_3(ascend: &mut [*mut u8]) {
        let new_size = idx_to_size(COUNT-1);
        let new = Layout::from_size_align(new_size, ALIGN).unwrap();
        for i in (0..COUNT / 2).rev() {
            let (p0, p1, old_size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
            assert!(old_size < new_size);
            let old = Layout::from_size_align(old_size, ALIGN).unwrap();

            ascend[2*i+1] = reallocate(p1, old.clone(), new.clone());
            sanity_check(&*ascend);

            ascend[2*i] = reallocate(p0, old.clone(), new.clone());
            sanity_check(&*ascend);
        }
    }

    // Test 4: turn the square back into a triangle, bottom to top.
    unsafe fn test_4(ascend: &mut [*mut u8]) {
        let old_size = idx_to_size(COUNT-1);
        let old = Layout::from_size_align(old_size, ALIGN).unwrap();
        for i in (0..COUNT / 2).rev() {
            let (p0, p1, new_size) = (ascend[2*i], ascend[2*i+1], idx_to_size(i));
            assert!(new_size < old_size);
            let new = Layout::from_size_align(new_size, ALIGN).unwrap();

            ascend[2*i+1] = reallocate(p1, old.clone(), new.clone());
            sanity_check(&*ascend);

            ascend[2*i] = reallocate(p0, old.clone(), new.clone());
            sanity_check(&*ascend);
        }
    }
}
