Require Import coqutil.Word.Bitwidth.

Declare Scope word_scope.

Infix "^+" := Zmod.add  (at level 50, left associativity) : word_scope.
Infix "^-" := Zmod.sub  (at level 50, left associativity) : word_scope.
Infix "^*" := Zmod.mul  (at level 40, left associativity) : word_scope.
Infix "^<<" := Zmod.slu  (at level 37, left associativity) : word_scope.
Infix "^>>" := Zmod.sru  (at level 37, left associativity) : word_scope.

(* squeeze a Z into a word (beat it with a / to make it smaller) *)
Notation "/[ x ]" := (Zmod.of_Z _ x) (format "/[ x ]") : word_scope.
(* \ is the open (removed) lid of the modulo box imposed by words, *)
Notation "\[ x ]" := (Zmod.unsigned x) (format "\[ x ]") : word_scope.
