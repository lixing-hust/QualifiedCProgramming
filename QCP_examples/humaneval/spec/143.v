(* def words_in_sentence(sentence):
"""
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
Input: sentence = "This is a test"
Output: "is"

Example 2:
Input: sentence = "lets go for swimming"
Output: "go for"

Constraints:
* 1 <= len(sentence) <= 100
* sentence contains only letters
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* IsPrime states the mathematical trial-divisor characterization: no
   divisor from 2 through the square root exists. *)
Definition IsPrime (n : nat) : Prop :=
  2 <= n /\
  forall d : nat, 2 <= d -> d * d <= n -> n mod d <> 0.

(* A word segment contains no spaces.  Empty segments are allowed so this
   relation also represents leading, trailing, or consecutive spaces. *)
Definition SpaceFree (word : string) : Prop :=
  ~ In " "%char (list_ascii_of_string word).

(* words occur in sentence in this order, separated by its original spaces. *)
Definition SentenceWords (sentence : string) (words : list string) : Prop :=
  String.concat " " words = sentence /\
  Forall SpaceFree words.

(* selected contains exactly the words whose lengths are prime, in their
   original order. *)
Inductive PrimeLengthWords : list string -> list string -> Prop :=
| prime_words_nil :
    PrimeLengthWords [] []
| prime_words_keep : forall word words selected,
    IsPrime (String.length word) ->
    PrimeLengthWords words selected ->
    PrimeLengthWords (word :: words) (word :: selected)
| prime_words_drop : forall word words selected,
    ~ IsPrime (String.length word) ->
    PrimeLengthWords words selected ->
    PrimeLengthWords (word :: words) selected.

(* 约束：1 <= 长度 <= 100；内容为英文字母或空格 *)
Definition problem_143_pre (sentence : string) : Prop :=
  let l := list_ascii_of_string sentence in
  1 <= List.length l /\ List.length l <= 100 /\
  Forall (fun c =>
    let n := nat_of_ascii c in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence : string) (output : string) : Prop :=
  exists words selected,
    SentenceWords sentence words /\
    PrimeLengthWords words selected /\
    output = String.concat " " selected.
