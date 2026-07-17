(* You will be given a string of words separated by commas or spaces. Your task is
to split the string into words and return an array of the words.

For example:
words_string("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
words_string("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.



Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true | _ => false end.

(* A delimiter block may be empty; this covers the optional leading and trailing
   delimiters as well as runs of consecutive delimiters. *)
Definition delimiter_block (block : list ascii) : Prop :=
  Forall (fun c => is_delimiter c = true) block.

(* Every returned word is nonempty and contains no delimiter. *)
Definition word_block (word : list ascii) : Prop :=
  word <> [] /\
  Forall (fun c => is_delimiter c = false) word.

(* The input consists of a leading delimiter block followed by the returned
   words, each paired with the delimiter block after it.  Every block between
   two words is nonempty, so a delimiter is required at each word boundary. *)
Definition words_string_rel
    (input : list ascii) (words : list (list ascii)) : Prop :=
  exists leading trailing_blocks,
    delimiter_block leading /\
    length trailing_blocks = length words /\
    Forall delimiter_block trailing_blocks /\
    Forall (fun block => block <> []) (removelast trailing_blocks) /\
    Forall word_block words /\
    input =
      leading ++
      concat
        (map (fun pair => fst pair ++ snd pair)
             (combine words trailing_blocks)).

(* 输入为仅包含字母、逗号或空格的字符列表 *)
Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  exists words,
    words_string_rel (list_ascii_of_string s) words /\
    output = map string_of_list_ascii words.

