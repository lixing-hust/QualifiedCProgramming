(* """ Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string and return list of integers corresponding to how many beats does each
not last.

Here is a legend:
'o' - whole note, lasts four beats
'o|' - half note, lasts two beats
'.|' - quater note, lasts one beat

>>> parse_music('o o| .| o| o| .| .| .| .| o o')
[4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
""" *)

(* 
*)

Require Import Ascii String List.
Import ListNotations.
Open Scope string_scope.

Definition MusicToken (token : string) : Prop :=
  token = "o" \/ token = "o|" \/ token = ".|".

Definition SingleSpaceSeparated (input : string) (tokens : list string) : Prop :=
  String.concat " " tokens = input /\ Forall MusicToken tokens.

Definition MusicBeat (token : string) (beat : nat) : Prop :=
  (token = "o" /\ beat = 4) \/
  (token = "o|" /\ beat = 2) \/
  (token = ".|" /\ beat = 1).

Definition MusicBeats (tokens : list string) (output : list nat) : Prop :=
  Forall2 MusicBeat tokens output.

Definition problem_17_pre (input : string) : Prop :=
  exists tokens, SingleSpaceSeparated input tokens.

Definition problem_17_spec (input : string) (output : list nat) : Prop :=
  exists tokens,
    SingleSpaceSeparated input tokens /\
    MusicBeats tokens output.
