Require Import Arith List.

(* ============================================================
   SECTION 1: JVM Implementation
   ============================================================ *)

Definition Memory : Type := list nat.
Definition Stack : Type := list nat.
Definition Address : Type := nat.

Fixpoint read (addr : Address) (default : nat) (mem : Memory) : nat :=
match addr, mem with
| _, nil => default
| 0, x :: _ => x
| S n, _ :: xs => read n default xs
end.

Fixpoint write (addr : Address) (value : nat) (mem : Memory) : Memory :=
match addr, mem with
| _, nil => nil
| 0, _ :: xs => value :: xs
| S n, x :: xs => x :: write n value xs
end.

Inductive Instruction : Type :=
| load  : Address -> Instruction
| const : nat ->     Instruction
| add   :            Instruction
| sub   :            Instruction
| mul   :            Instruction
| store : Address -> Instruction
| goto  : Address -> Instruction
| ifeq  : Address -> Instruction
| halt  :            Instruction.

Definition Program : Type := Address -> Instruction.

Record Machine : Type := {
  pc : Address;
  program : Program;
  locals : Memory;
  stack : Stack;
}.

Definition fetch (m : Machine) : Instruction := program m (pc m).

Definition execute_single_instruction (m : Machine) : Machine :=
match fetch m, stack m with
| load addr, s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := read addr 0 (locals m) :: s;
|}
| const c, s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := c :: s;
|}
| add, x :: y :: s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := x + y :: s;
|}
| sub, x :: y :: s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := y - x :: s;
|}
| mul, x :: y :: s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := y * x :: s;
|}
| goto addr, s => {|
  pc := addr;
  program := program m;
  locals := locals m;
  stack := s;
|}
| ifeq addr, 0 :: s => {|
  pc := addr;
  program := program m;
  locals := locals m;
  stack := s;
|}
| ifeq addr, _ :: s => {|
  pc := pc m + 1;
  program := program m;
  locals := locals m;
  stack := s;
|} 
| store addr, x :: s => {|
  pc := pc m + 1;
  program := program m;
  locals := write addr x (locals m);
  stack := s;
|}
| _, _ => m
end.

Fixpoint execute_n_instructions (n : nat) (m : Machine) : Machine :=
match n with
| 0 => m
| S n => execute_n_instructions n (execute_single_instruction m)
end.

Lemma execute_instruction_succ (a : nat) : forall m,
  execute_single_instruction (execute_n_instructions a m) = execute_n_instructions (S a) m.
Proof.
  induction a.
  - intros m. simpl. reflexivity.
  - intros m. simpl. apply IHa.
Qed.

Lemma execute_plus_instructions (a : nat) : forall b m,
  execute_n_instructions (a + b) m = execute_n_instructions a (execute_n_instructions b m).
Proof.
  induction a.
  - intros b m. simpl. reflexivity.
  - intros b m. simpl. rewrite IHa. rewrite execute_instruction_succ. reflexivity.
Qed.

(* ============================================================
   SECTION 2: Exponential Program
   ============================================================ *)

Definition expt (n m : nat) : nat := n ^ m.

Fixpoint expt_iter (n m acc : nat) :=
match m with
| 0 => acc
| S m' => expt_iter n m' (n * acc)
end.

Lemma expt_iter_helper : forall m n acc,
  expt_iter n m acc = acc * expt n m.
Proof.
  intros m n.
  induction m as [| m' IHm'].
  - intros acc. simpl.
    rewrite Nat.mul_1_r. 
    reflexivity.
  - intros acc. simpl.
    rewrite IHm'.
    rewrite (Nat.mul_comm n acc).
    rewrite Nat.mul_assoc.
    reflexivity.
Qed.

Theorem expt_iter_equivalent (n m : nat) : 
  expt_iter n m 1 = expt n m.
Proof.
  rewrite expt_iter_helper.
  apply Nat.mul_1_l.
Qed.

Definition expt_program : Program := fun pc =>
match pc with
| 0 =>  const 1
| 1 =>  store 2
| 2 =>  load 1
| 3 =>  ifeq 14
| 4 =>  load 1
| 5 =>  const 1
| 6 =>  sub
| 7 =>  store 1
| 8 =>  load 0
| 9 =>  load 2
| 10 => mul
| 11 => store 2
| 12 => goto 2
| 13 => load 2
| _ => halt
end.

Definition read_acc (m : Machine) : nat := read 2 0 (locals m).

Fixpoint expt_loop_instructions (m : nat) : nat :=
match m with
| 0 => 2
| S m => 11 + expt_loop_instructions m
end.

Definition expt_total_instructions (m : nat) : nat :=
2 + expt_loop_instructions m.

Definition jvm_expt (n m : nat) : Machine :=
execute_n_instructions (expt_total_instructions m) {|
  pc := 0;
  program := expt_program;
  locals := n :: m :: 0 :: nil;
  stack := nil
|}.

Lemma expt_loop_correct : forall m n acc,
  execute_n_instructions (expt_loop_instructions m) {|
    pc := 2;
    program := expt_program;
    locals := n :: m :: acc :: nil;
    stack := nil
  |} = {|
    pc := 14;
    program := expt_program;
    locals := n :: 0 :: expt_iter n m acc :: nil;
    stack := nil
  |}.
Proof.
  intros m n.
  induction m as [| m' IHm'].
  - intros acc. simpl. reflexivity.
  - intros acc.
    change (expt_loop_instructions (S m')) with (11 + expt_loop_instructions m').
    rewrite Nat.add_comm.
    rewrite execute_plus_instructions.
    change (execute_n_instructions 11 _) with {| 
      pc := 2; 
      program := expt_program;
      locals := n :: (m' - 0) :: n * acc :: nil; 
      stack := nil 
    |}.
    rewrite Nat.sub_0_r.
    apply IHm'.
Qed.

Theorem jvm_expt_correct (n m : nat) : read_acc (jvm_expt n m) = expt n m.
Proof.
  unfold jvm_expt, expt_total_instructions, read_acc.
  rewrite Nat.add_comm, execute_plus_instructions.
  cbn.
  rewrite expt_loop_correct.
  simpl.
  apply expt_iter_equivalent.
Qed.

Theorem jvm_expt_halts (n m : nat) : fetch (jvm_expt n m) = halt.
Proof.
  unfold jvm_expt, expt_total_instructions.
  rewrite Nat.add_comm. rewrite execute_plus_instructions.
  cbn.
  rewrite expt_loop_correct.
  reflexivity.
Qed.