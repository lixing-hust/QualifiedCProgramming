(* Given a string s and a natural number n, you have been tasked to implement
a function that returns a list of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty list.
Note: you may assume the input string contains only letters and spaces.
Examples:
select_words("Mary had a little lamb", 4) ==> ["little"]
select_words("Mary had a little lamb", 3) ==> ["Mary", "lamb"]
select_words("simple white space", 2) ==> []
select_words("Hello world", 4) ==> ["world"]
select_words("Uncle sam", 3) ==> ["Uncle"] *)

Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.



Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char => true | "e"%char => true | "i"%char => true | "o"%char => true | "u"%char => true
  | "A"%char => true | "E"%char => true | "I"%char => true | "O"%char => true | "U"%char => true
  | _ => false
  end.

Definition is_letter (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) ||
  ((Nat.leb 97 n) && (Nat.leb n 122)).

Definition is_consonant (c : ascii) : bool :=
  is_letter c && negb (is_vowel c).

Definition count_consonants (w : list ascii) : nat :=
  length (filter is_consonant w).

Definition only_spaces (xs : list ascii) : Prop :=
  Forall (fun c => c = " "%char) xs.

Definition nonempty_spaces (xs : list ascii) : Prop :=
  xs <> [] /\ only_spaces xs.

Definition word_chars (w : list ascii) : Prop :=
  w <> [] /\ Forall (fun c => c <> " "%char) w.

Definition separated_words
    (front : list (list ascii)) (seps : list (list ascii)) (last : list ascii)
    : list ascii :=
  (concat (map (fun ws => ((fst ws) ++ (snd ws))%list) (combine front seps)) ++ last)%list.

Definition split_words_shape (s : list ascii) (words : list (list ascii)) : Prop :=
  (words = [] /\ only_spaces s) \/
  exists leading trailing front last seps,
    words = (front ++ [last])%list /\
    Forall word_chars (front ++ [last]) /\
    only_spaces leading /\
    only_spaces trailing /\
    Forall nonempty_spaces seps /\
    length seps = length front /\
    s = (leading ++ separated_words front seps last ++ trailing)%list.

Definition select_words_impl (words : list (list ascii)) (n : nat) : list (list ascii) :=
  filter (fun w => Nat.eqb (count_consonants w) n) words.

(* 字符串只含字母与空格 *)
Definition problem_117_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  exists words,
    split_words_shape (list_ascii_of_string s) words /\
    output = map string_of_list_ascii (select_words_impl words n).
