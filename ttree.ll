;; ttree.ll - Tournament tree structure for
;; <O(n log n), O(log n)>- Range Maximum Query (RMQ) in LLVM IR
;; -----------------------------------------------------------------
;; Author: Ruijie Fang 
;;
;; ruijief:
;; SYNOPSIS:
;; The dynamic (online) Range Maximum Query problem is a well-known problem
;; in algorithm design, defined as follows:
;; Given an initial sequence of n integers stored in an array a indexed from 0 to n-1,
;; answer m queries of the form RMQ(l, r).
;;  - RMQ(l, r) - Returns the largest integer in a[l...r], inclusive.
;;      i.e. RMQ(l, r) = max{a[i]; l<=i<=r}.
;;
;; There exists a well-known solution to this problem using tournament trees.
;; Tournament trees (*: More commenly known as segment trees in competitive programming/
;; information olympiads literature, but we call them tournament trees here to
;; disambiguate from segment trees in computational geometry) are perfect binary trees
;; built on top of the original array, a, where the leaf nodes represent the elements
;; inside the original array, and each internal node is the max of its two children.
;; For example, the array {1, 2, 3, 4, 5, 6} has the following tournament tree:
;;
;;            +------------6----------+
;;    +-------4-------+               |
;; +--2---+       +---4---+       +---6---+
;; 1      2       3       4       5       6
;;
;; It can be shown that element value modifications and RMQ queries can be implemented
;; in O(log n) time each for the tournament tree (see e.g. https://cp-algorithms.com/data_structures/segment_tree.html).
;;
;; In our code, we perform n "build" calls to build the tree in top-down fashion,
;; inserting the n elements inside the array 'a' into the tree, starting from a tree of 0's.
;; Each 'build' call takes logarithmic time, so it takes O(n log n) time to build the entire
;; tree from scratch. Afterwards, we perform a single query on the range a[0...n-1] to
;; query for the overall minimum of the entire tree. Our code can be easily augmented to
;; support other querying other subarray intervals. Our algorithm, in general, follows
;; the code documented in the link above.
;;
;; In addition, we use an array-based representation of a complete binary tree, where
;; the root is located at index 0, the left child of a parent at index p at index 2*p+1,
;; and the right child is located at 2*p+2.
;;
;; Although such a representation is rather memory-consuming in the worst case, we
;; allocate roughly 5*n memory to represent an array of size n, which is usually good
;; enough for the average case (and works for our test cases in studenttests.ml).
;;
;; The array representing the tree is heap-allocated via helper functions defined in
;; ttree_cinterop.c, and is freed after use. In addition, since LLVMlite does not support
;; casting pointers, we do pointer arithmetic to find array indices inside the C code, not
;; the LLVMlite code. (Also, since we do heap allocation, getelementptr is not very useful
;; when computing the array offset given an array index). But we try very hard to keep all the
;; main components of the program inside LLVMlite IR.
;;
;; P.S. The name for the "tournament" tree comes from the fact that each two child
;; nodes undergo a "tournament" to determine the parent, and is used in previous literature
;; on data structures for RMQ (See http://www.cs.umanitoba.ca/~durocher/research/pubs/durocherIanFest2013.pdf, pp.4).
;;
;; COMPILING
;; -----------
;; * LLVM/clang compilation: Place `ttree_cinterop.c` and `ttree.ll` inside the same folder.
;; Then issue the command `clang -S -emit-llvm ttree_cinterop.c` to compile the supporting C
;; functions into LLVM IR. Next, pipe this file into the LLVM IR code of cinterop: `cat ttree.ll >> ttree_cinterop.ll`.
;; Finally, issue the command `clang ttree_cinterop.ll` to compile everything into executable binary.
;; * COS320 backend: Compile your project using make. Then `./main.native --execute-x86 ttree.ll ttree_cinterop.ll`
;; * Grading: Use our provided `studenttest.ml` file and perform `make test`.
;;
;; USAGE
;; --------
;; Our tree array is heap-allocated; contents of the array `a` are read in from arguments.
;; The format is:
;; ./a.out <n> <a_0> <a_1> <a_2> ... <a_n-1>
;; A successful run will output the largest element inside the array `a` inputted via arguments list.

;; allocates a new array of int64's on the heap
define i64* @new_array(i64 %size) {
  %1 = mul i64 8, %size
  %2 = call i64* @ll_malloc(i64 %1)
  ret i64* %2
}

;; frees an array of int64's
define i64 @free_array(i64* %t) {
  %1 = call i64 @ll_free(i64* %t)
  ret i64 %1
}

;; retrieves the content of i64 a[idx]
define i64 @array_get(i64* %a, i64 %idx) {
  %1 = call i64* @ll_int64_array_idx(i64* %a, i64 %idx)
  %2 = load i64, i64* %1
  ret i64 %2
}

;; stores value v into i64 a[idx]
define i64 @array_set(i64* %a, i64 %idx, i64 %v) {
  %1 = call i64* @ll_int64_array_idx(i64* %a, i64 %idx)
  store i64 %v, i64* %1
  ret i64 0
}

;; left child = 2*p+1
define i64 @left_child(i64 %p) {
  %1 = mul i64 2, %p
  %2 = add i64 %1, 1
  ret i64 %2
}

;; right child = 2*p+2
define i64 @right_child(i64 %p) {
  %1 = mul i64 2, %p
  %2 = add i64 %1, 2
  ret i64 %2
}

;; calculates l + (r-l) / 2
define i64 @left_until(i64 %l, i64 %r) {
  %1 = sub i64 %r, %l ;; r - l
  %2 = lshr i64 %1, 1 ;; (r - l) >> 1 == (r - l) / 2
  %3 = add i64 %l, %2
  ret i64 %3
}

;; calculates l + (r - l) / 2 + 1
define i64 @right_from(i64 %l, i64 %r) {
  %1 = call i64 @left_until(i64 %l, i64 %r)
  %2 = add i64 %1, 1
  ret i64 %2
}

;; max function. returns the max of two i64 integers
define i64 @max(i64 %a, i64 %b) {
  %1 = icmp slt i64 %a, %b ;; a < b ?
  br i1 %1, label %return_b, label %return_a
  return_a:
  ret i64 %a
  return_b:
  ret i64 %b
}

;; builds a tournament tree starting from a[idx]
define i64 @build(i64* %a, i64 %p, i64 %l, i64 %r, i64 %idx, i64 %val) {
  %1 = icmp slt i64 %idx, %l
  %2 = icmp sgt i64 %idx, %r
  %3 = or i1 %1, %2
  br i1 %3, label %build_exit, label %build_next
  build_next:
  %4 = icmp eq i64 %l, %r
  br i1 %4, label %build_basecase, label %build_recur
  build_basecase:
  %5 = call i64 @array_set(i64* %a, i64 %p, i64 %val)
  br label %build_exit
  build_recur:
  %lch = call i64 @left_child(i64 %p)
  %rch = call i64 @right_child(i64 %p)
  %lch_right = call i64 @left_until(i64 %l, i64 %r)
  %rch_left = call i64 @right_from(i64 %l, i64 %r)
  %6 = call i64 @build(i64* %a, i64 %lch, i64 %l, i64 %lch_right, i64 %idx, i64 %val)
  %7 = call i64 @build(i64* %a, i64 %rch, i64 %rch_left, i64 %r, i64 %idx, i64 %val)
  %lch_val = call i64 @array_get(i64* %a, i64 %lch)
  %rch_val = call i64 @array_get(i64* %a, i64 %rch)
  %max_of_two = call i64 @max(i64 %lch_val, i64 %rch_val)
  %8 = call i64 @array_set(i64* %a, i64 %p, i64 %max_of_two)
  br label %build_exit
  build_exit:
  ret i64 0
}

;; Returns RMQ(A[L...R]) given sub-tree at a[p] representing
;; interval l...r.
define i64 @range_maximum(i64* %a, i64 %p, i64 %l, i64 %r, i64 %L, i64 %R) {

  %1 = icmp sgt i64 %L, %r ;; L > r ?
  %2 = icmp slt i64 %R, %l ;; R < l ?
  %3 = or i1 %1, %2 ;; L > r || R < l ?
  br i1 %1, label %exit_default, label %rangemax_next
  rangemax_next:
  %4 = icmp sle i64 %r, %R ;; r <= R ?
  %5 = icmp sge i64 %l, %L ;; l >= L ?
  %6 = and i1 %4, %5 ;; r <= R && l >= L ?
  br i1 %6, label %rangemax_basecase, label %rangemax_else
  rangemax_basecase:
  %7 = call i64 @array_get(i64* %a, i64 %p)
  ret i64 %7
  rangemax_else:
  %lch = call i64 @left_child(i64 %p)
  %rch = call i64 @right_child(i64 %p)
  %lch_right = call i64 @left_until(i64 %l, i64 %r)
  %rch_left = call i64 @right_from(i64 %l, i64 %r)
  %lch_range_max = call i64 @range_maximum(i64* %a, i64 %lch, i64 %l, i64 %lch_right, i64 %L, i64 %R)
  %rch_range_max = call i64 @range_maximum(i64* %a, i64 %rch, i64 %rch_left, i64 %r, i64 %L, i64 %R)
  %overall_max = call i64 @max(i64 %lch_range_max, i64 %rch_range_max)
  ret i64 %overall_max
  exit_default:
  ret i64 0
}

;; entry function.
;; format:
;; <program> <size of array> <arr0> <arr1> ... <arr_n-1>
define i64 @main(i64 %argc, i8** %argv) {
  ;; arglen = argc - 1
  %arglen = sub i64 %argc, 1
  %1 = icmp ne i64 %arglen, 0
  ;; if arglen == 0 then bye, else go ahead.
  br i1 %1, label %go, label %bye
  go:
  ;; length of array
  %2 = getelementptr i8*, i8** %argv, i64 1
  %d2 = load i8*, i8** %2
  %n = call i64 @ll_atoi64(i8* %d2)
  %til = sub i64 %n, 1
  ;; allocate array
  %_sz1 = mul i64 %n, 5
  %a = call i64* @new_array(i64 %_sz1)
  ;; loop setup
  %i = alloca i64
  store i64 0, i64* %i
  br label %loop
  loop:
  %3 = load i64, i64* %i
  %4 = icmp ne i64 %3, %n
  br i1 %4, label %loop_body, label %loop_end
  loop_body:
  %offset = add i64 %3, 2
  %5 = getelementptr i8*, i8** %argv, i64 %offset
  %d5 = load i8*, i8** %5
  %a_i = call i64 @ll_atoi64(i8* %d5)
  ; %t3 = call i64 @ll_print_int64(i64 %a_i)
  %6 = call i64 @build(i64* %a, i64 0, i64 0, i64 %til, i64 %3, i64 %a_i)
  %new_i = add i64 %3, 1
  store i64 %new_i, i64* %i
  br label %loop
  loop_end:
  ;; finished building the tree. Now do a single query.
  %result = call i64 @range_maximum(i64* %a, i64 0, i64 0, i64 %til, i64 0, i64 %til)
  ;; print out the result of RMQ.
  %____ = call i64 @ll_print_int64(i64 %result)
  br label %done
  done:
  ;; deallocate array
  %tmp = call i64 @free_array(i64* %a)
  br label %bye
  bye:
  ret i64 %result
}
