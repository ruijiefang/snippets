open Assert
open X86
open Simulator
open Asm
open Gradedtests

(*
ruijief: Our submission for student test is an O(n^2) dynamic programming
  algorithm for computing the longest increasing subsequence of an array a of
  int64's. Specifically, we iteratively compute the following recurrence:

    LIS_at(k):= max {LIS_at(j) ; 0<=j<k && a[j] <= a[i]}

  with LIS_at(k) denoting the length of a longest increasing subsequence ending
  at k. By definition, LIS(k) = max{LIS_at(j); 0<=j<k} is the longest increasing
  subsequence for a[0...k].

  The above recurrence translates into the following iterative C code:

  #define N 11
  static unsigned long a[N] = {1,6,3,4,56,2,3,6,54,8,5}; /* LIS = 5 */
  static unsigned long ltable[N];
  unsigned long lis(void)
  {
    unsigned long i, j, best = 0;
    ltable[0] = 1;
  outer_loop:
    for(i = 0L; i < N; ++i) {
      ltable[i] = 0;
  inner_loop:
      for(j = 0L; j < i; ++j) {
        if (a[j] <= a[i] && ltable[j] >= ltable[i]) ltable[i] = ltable[j];
  inner_loop_next:
      }
  outer_loop_end:
      ++ltable[i];
      if (ltable[i] > best) best = ltable[i];
    }
    return best;
  }

  We store the array `a` in the data section of the assembly program. Our
  assembly implementation is a direct translation of the above C program,
  returning the `best` variable in %Rax register.

  The lis function below takes in a list of data elements defining the array
  of data elements representing the array `a` to be computed and outputs an
  assembly program that computes the length of the longest increasing
  subsequence of that array.

  There are no function calls (Callq), so we don't really need to execute
  the caller/callee protocol(s). But this program does heavily involve
  pointer arithmetic and load/stores to the data section in memory.

  Our C solution is verified against another LIS solution that passed various
  Online Judge tests (such as LeetCode). Our Assembly implementation is
  verified against the C solution results as shown below.

  It is suggested that the grader come up with more test cases for
  longest increasing subsequence to further verify the correctness of this
  program.

  Note that, our "increasing" subsequence is defined as a "nondecreasing"
  subsequence but not a "strictly increasing" subsequence.
*)

(* Makes an empty list of Quad literals of size n. *)
let rec make_empty_list n = match n with
  | 0 -> []
  | k -> Quad (Lit 0L) :: (make_empty_list (n - 1))

let lis (a : data list) =
 let n = List.length a in [
 data "a" a ;
 data "ltable" (make_empty_list n) ;
 text "main" [ (* Main function entry. *)
   Movq, [~$0; ~%Rax]; (* best is in Rax *)
   Movq, [~$0; ~%Rdi]; (* i is in Rdi *)
   Movq, [~$1; ~%R08]; (* ltable[0] := 1; *)
   Movq, [~%R08; ~$$"ltable"] (* ltable[0] := 1 *)
 ];
 text "outer_loop" [
   Cmpq, [~$n; ~%Rdi]; (* i == n? *)
   J Eq, [~$$"exit"]; (* if yes, then exit. *)
   Leaq, [~$$"ltable"; ~%Rsi]; (* Store address of ltable into Rsi *)
   Movq, [~%Rdi; ~%Rdx]; (* Use Rdx to store the address of ltable[i] *)
   Imulq, [~$8; ~%Rdx]; (* Rdx := Rdx * 8 *)
   Addq, [~%Rdx; ~%Rsi]; (* Rsi := Rsi + Rdx = ltable + 8 * i *)
   Movq, [~$0; ~%R15];
   Movq, [~%R15; Ind2 (Rsi) ]; (* ltable[i] := 0 *)
   Movq, [~%R15; ~%R08]; (* R08 is j = 0 *)
   Jmp, [~$$"inner_loop"]
 ];
 text "outer_loop_end" [
   Leaq, [~$$"ltable"; ~%R09]; (* R09 = ltable *)
   Movq, [~%Rdi; ~%Rbx]; (* Rbx = i *)
   Imulq, [~$8; ~%Rbx]; (* Rbx = 8*i *)
   Addq, [~%Rbx; ~%R09]; (* R09 = Rbx * 8 + ltable = i*8 + ltable *)
   Movq, [Ind2 (R09); ~%R12]; (* R12 = ltable[i] *)
   Addq, [~$1; ~%R12]; (* R09 = R09 + 1 *)
   Movq, [~%R12; Ind2 (R09)]; (* ltable[i] = ltable[i] + 1; *)
   Cmpq, [~%Rax; ~%R12]; (*  ltable[i] > best? *)
   J Le, [~$$"outer_loop_next"]; (* if not, jump back to outer loop. *)
   Movq, [~%R12; ~%Rax]; (* otherwise, best = ltable[i] *)
   (*Go to inner loop*)
   Jmp, [~$$"outer_loop_next"]
 ];
 text "outer_loop_next" [
     Addq, [~$1; ~%Rdi]; (* i+= 1 *)
     Jmp, [~$$"outer_loop"] (* back to inner loop *)
 ];
 text "inner_loop" [
   Cmpq, [~%Rdi; ~%R08];
   J Eq, [~$$"outer_loop_end"]; (* if i==j, then exit inner loop *)
   (* Store a[j] into R09 *)
   Leaq, [~$$"a"; ~%R09]; (* load addr of label a into R09 *)
   Movq, [~%R08; ~%Rbx]; (* Rbx = j *)
   Imulq, [~$8; ~%Rbx];  (* Rbx = 8*j *)
   Addq, [~%Rbx; ~%R09]; (* R09 = R09 + Rbx = a + 8*j *)
   Movq, [Ind2 (R09); ~%R09];  (* R09 = a[j], R08 = j *)
   (*Store a[i] into R12*)
   Leaq, [~$$"a"; ~%R12]; (* R12 = a *)
   Movq, [~%Rdi; ~%Rbx]; (* Rbx = i *)
   Imulq, [~$8; ~%Rbx]; (* Rbx = i * 8 *)
   Addq, [~%Rbx; ~%R12]; (* R12 = R12 + Rbx = a + 8*i *)
   Movq, [Ind2 (R12); ~%R12]; (* R12 = a[i] *)
   Cmpq, [~%R12; ~%R09]; (* R09 <= R12 <=> a[j] <= a[i] ? *)
   J Gt, [~$$"inner_loop_next"];
   Leaq, [~$$"ltable"; ~%R09]; (* R09 = rtable *)
   Movq, [~%R08; ~%Rbx]; (*Rbx = j*)
   Imulq, [~$8; ~%Rbx]; (*Rbx = 8*j*)
   Addq, [~%Rbx; ~%R09]; (* R09 = R09 + rbx = ltable + 8*j *)
   Movq, [Ind2 (R09); ~%R09]; (* R09 = ltable[j], R08 = j *)
   Leaq, [~$$"ltable"; ~%R12]; (* R12 = ltable *)
   Movq, [~%Rdi; ~%Rbx]; (* Rbx = i *)
   Imulq, [~$8; ~%Rbx]; (* Rbx = 8*i *)
   Addq, [~%Rbx; ~%R12]; (* R12 = R12 + Rbx = ltable + 8*i *)
   Movq, [Ind2 (R12); ~%R12]; (* R12 = ltable[i] *)
   Cmpq, [~%R12; ~%R09]; (* R09 >= R12 <=> ltable[j] >= ltable[i] *)
   J Lt, [~$$"inner_loop_next"];
   (* ltable[i] = ltable[j] *)
   Leaq, [~$$"ltable"; ~%R12]; (* R12 = ltable *)
   Addq, [~%Rbx; ~%R12]; (* R12 = ltable + 8*i*)
   Movq, [~%R09; Ind2 (R12)]; (* ltable[i] = R09 = ltable[j] *)
   Jmp, [~$$"inner_loop_next"]
 ];
 text "inner_loop_next" [
   Addq, [~$1; ~%R08]; (* j+= 1 *)
   Jmp, [~$$"inner_loop"] (* back to inner loop *)
 ];
 text "exit" [
   Retq, [] (* return best in Rax *)
 ]
]


(* Kexinjin: gcd in C:
#include <stdio.h>
int main()
{
    int n1, n2;
    while(n1!=n2)
    {
        if(n1 > n2)
            n1 -= n2;
        else
            n2 -= n1;
    }
    return n1;
}
The `gcd` function below is a literal translation of the above C code into
x86 assembly.
*)
let gcd n m =[ text "main"
                        [ Movq, [~$n; ~%Rax]
                        ; Movq, [~$m; ~%Rdi]
                        ]
                 ; text "loop"
                        [Cmpq, [~%Rdi; ~%Rax]
                        ;J Eq, [~$$"exit"]
                        ; Cmpq, [~%Rdi; ~%Rax]
                        ; J Le, [~$$"else"]
                        ; Subq, [~%Rdi; ~%Rax]
                        ; Jmp, [~$$"loop"]
                        ]
                  ; text "else"
                        [ Subq, [~%Rax; ~%Rdi]
                         ; Jmp, [~$$"loop"]
                         ]
                  ; text "exit"
                         [
                           Retq,  []
                         ]
                  ]


let provided_tests_gcd : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
     ("gcd(12,100)",program_test (gcd 12 100) 4L);
     ("gcd(123321,321123)",program_test (gcd 123321 321123) 1221L);
  ]);

]

let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    ("LIS", program_test (lis [
      Quad (Lit 1L);
      Quad (Lit 6L);
      Quad (Lit 3L);
      Quad (Lit 4L);
      Quad (Lit 56L);
      Quad (Lit 2L);
      Quad (Lit 3L);
      Quad (Lit 6L);
      Quad (Lit 54L);
      Quad (Lit 8L);
      Quad (Lit 5L)
    ]) 5L);
    (* lis[10,9,2,5,3,7,101,18] = 4 *)
    ("LIS", program_test (lis [
      Quad (Lit 10L);
      Quad (Lit 9L);
      Quad (Lit 2L);
      Quad (Lit 5L);
      Quad (Lit 3L);
      Quad (Lit 7L);
      Quad (Lit 101L);
      Quad (Lit 18L)
    ]) 4L);
    (* lis[5, 18, 6, 19, 9, 8, 12, 1, 10, 7] = 4 *)
    ("LIS", program_test (lis [
      Quad (Lit 5L);
      Quad (Lit 18L);
      Quad (Lit 6L);
      Quad (Lit 19L);
      Quad (Lit 9L);
      Quad (Lit 8L);
      Quad (Lit 12L);
      Quad (Lit 1L);
      Quad (Lit 10L);
      Quad (Lit 7L)
    ]) 4L);
    (* lis[13, 12, 9, 8, 15, 7, 19, 18, 14, 6] = 3 *)
    ("LIS", program_test (lis [
      Quad (Lit 13L);
      Quad (Lit 12L);
      Quad (Lit 9L);
      Quad (Lit 8L);
      Quad (Lit 15L);
      Quad (Lit 7L);
      Quad (Lit 19L);
      Quad (Lit 18L);
      Quad (Lit 14L);
      Quad (Lit 6L)
    ]) 3L);
    (* lis[19, 13, 12, 11, 3, 17, 4, 10, 7, 6] = 3 *)
    ("LIS", program_test (lis [
      Quad (Lit 19L);
      Quad (Lit 13L);
      Quad (Lit 12L);
      Quad (Lit 11L);
      Quad (Lit 3L);
      Quad (Lit 17L);
      Quad (Lit 4L);
      Quad (Lit 10L);
      Quad (Lit 7L);
      Quad (Lit 6L)
    ]) 3L);
    (* lis[1, 16, 10, 12, 20, 7, 18, 17, 2, 3] = 4 *)
    ("LIS", program_test (lis [
      Quad (Lit 1L);
      Quad (Lit 16L);
      Quad (Lit 10L);
      Quad (Lit 12L);
      Quad (Lit 20L);
      Quad (Lit 7L);
      Quad (Lit 18L);
      Quad (Lit 17L);
      Quad (Lit 2L);
      Quad (Lit 3L)
    ]) 4L);
    (* lis[7, 11, 1, 19, 20, 6, 13, 15, 16, 18] = 6 *)
    ("LIS", program_test (lis [
      Quad (Lit 7L);
      Quad (Lit 11L);
      Quad (Lit 1L);
      Quad (Lit 19L);
      Quad (Lit 20L);
      Quad (Lit 6L);
      Quad (Lit 13L);
      Quad (Lit 15L);
      Quad (Lit 16L);
      Quad (Lit 18L)
    ]) 6L);
    (* lis[0,0,0,0,0,0,0,3,3,3,3,3,3,4,4,4,4,4,4,4,4,1,0] = 21 *)
    ("LIS", program_test (lis [
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 0L);
      Quad (Lit 3L);
      Quad (Lit 3L);
      Quad (Lit 3L);
      Quad (Lit 3L);
      Quad (Lit 3L);
      Quad (Lit 3L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 4L);
      Quad (Lit 1L);
      Quad (Lit 0L)
    ]) 21L)
  ]);

]
