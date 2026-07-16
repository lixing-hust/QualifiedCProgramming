(* You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning and ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
get_closest_vowel("yogurt") ==> "u"
get_closest_vowel("FULL") ==> "U"
get_closest_vowel("quick") ==> ""
get_closest_vowel("ab") ==> ""*)

Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* Check whether a character is a vowel (case sensitive). *)
Definition is_vowel (c : ascii) : Prop :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => True
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => True
  | _ => False
  end.

(* Check whether a character is an English letter. *)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

Definition is_consonant (c : ascii) : Prop :=
  is_alpha c /\ ~ is_vowel c.

(* problem_118_pre requires all characters to be English letters. *)
Definition problem_118_pre (word : string) : Prop :=
  Forall is_alpha (list_ascii_of_string word).

(* The character at [i] is a vowel with a consonant on either side. *)
Definition vowel_between_consonants
    (word : string) (i : nat) (vowel : ascii) : Prop :=
  1 <= i < String.length word - 1 /\
  exists left right,
      String.get (i - 1) word = Some left /\
      String.get i word = Some vowel /\
      String.get (i + 1) word = Some right /\
      is_consonant left /\ is_vowel vowel /\ is_consonant right.

(* Return the rightmost vowel between two consonants, if one exists. *)
Definition problem_118_spec (word result : string) : Prop :=
  (exists i vowel,
      vowel_between_consonants word i vowel /\
      (forall j other,
          i < j -> ~ vowel_between_consonants word j other) /\
      result = String vowel EmptyString)
  \/
  ((forall i vowel, ~ vowel_between_consonants word i vowel) /\
   result = EmptyString).
