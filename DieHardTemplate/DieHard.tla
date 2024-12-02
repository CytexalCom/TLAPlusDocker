------------------------------ MODULE DieHard ------------------------------
EXTENDS Naturals

VARIABLES ThreeGallon, FiveGallon

Init ==
  /\ ThreeGallon = 0
  /\ FiveGallon = 0

(*Checks the capacity of the jugs*)
TypeOK ==
  /\ ThreeGallon >= 0
  /\ ThreeGallon <= 3
  /\ FiveGallon >= 0
  /\ FiveGallon <= 5

FillFiveGallon ==
  /\ FiveGallon' = 5
  /\ ThreeGallon' = ThreeGallon

EmptyFiveGallon ==
  /\ FiveGallon' = 0
  /\ ThreeGallon' = ThreeGallon

FillThreeGallon ==
  /\ ThreeGallon' = 3
  /\ FiveGallon' = FiveGallon

EmptyThreeGallon ==
  /\ ThreeGallon' = 0
  /\ FiveGallon' = FiveGallon

PourThreeToFive ==
  /\ FiveGallon' = IF ThreeGallon + FiveGallon > 5 THEN 5 ELSE ThreeGallon + FiveGallon
  /\ ThreeGallon' = ThreeGallon - (FiveGallon' - FiveGallon)

PourFiveToThree ==
  /\ ThreeGallon' = IF FiveGallon + ThreeGallon > 3 THEN 3 ELSE FiveGallon + ThreeGallon
  /\ FiveGallon' = FiveGallon - (ThreeGallon' - ThreeGallon)

NeverFourInFive ==
  \neg (FiveGallon = 4)

Next ==
  \/ FillFiveGallon
  \/ EmptyFiveGallon
  \/ FillThreeGallon
  \/ EmptyThreeGallon
  \/ PourThreeToFive
  \/ PourFiveToThree
=============================================================================
