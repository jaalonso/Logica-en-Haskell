module FormasNormales_Spec (main, spec) where

import SintaxisSemantica
import FormasNormales
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "FormasNormales" $ do
    it "esEquivalente ej 1" $
      esEquivalente (p <--> q) ((p --> q) /\ (q --> p))
      `shouldBe` True
    it "esEquivalente ej 2" $
      esEquivalente (p --> q)  ((no p) \/ q)
      `shouldBe` True
    it "esEquivalente ej 3" $
      esEquivalente (p /\ q)   (no ((no p) \/ (no q)))
      `shouldBe` True
    it "esEquivalente ej 4" $
      esEquivalente (p \/ q)   (no ((no p) /\ (no q)))
      `shouldBe` True
    it "eliminaEquivalencias ej 1" $
      eliminaEquivalencias (p <--> q)
      `shouldBe`((p --> q) /\ (q --> p))
    it "eliminaEquivalencias ej 2" $
      eliminaEquivalencias ((p <--> q) /\ (q <--> r))
      `shouldBe`(((p --> q) /\ (q --> p)) /\ ((q --> r) /\ (r --> q)))
    it "eliminaImplicaciones ej 1" $
      eliminaImplicaciones (p --> q)
      `shouldBe`(no p \/ q)
    it "eliminaImplicaciones ej 2" $
      eliminaImplicaciones (eliminaEquivalencias (p <--> q))
      `shouldBe`((no p \/ q) /\ (no q \/ p))
    it "interiorizaNegacion ej 1" $
      interiorizaNegacion (no (no p))
      `shouldBe` p
    it "interiorizaNegacion ej 2" $
      interiorizaNegacion (no (p /\ q))
      `shouldBe` (no p \/ no q)
    it "interiorizaNegacion ej 3" $
      interiorizaNegacion (no (p \/ q))
      `shouldBe` (no p /\ no q)
    it "interiorizaNegacion ej 4" $
      interiorizaNegacion (no (no (p \/ q)))
      `shouldBe` (p \/ q)
    it "interiorizaNegacion ej 5" $
      interiorizaNegacion (no ((no p) \/ q))
      `shouldBe` (p /\ no q)
    it "formaNormalNegativa ej 1" $
      formaNormalNegativa (p <--> q)
      `shouldBe`((no p \/ q) /\ (no q \/ p))
    it "formaNormalNegativa ej 2" $
      formaNormalNegativa ((p \/ (no q)) --> r)
      `shouldBe`((no p /\ q) \/ r)
    it "formaNormalNegativa ej 3" $
      formaNormalNegativa ((p /\ (q --> r)) --> s)
      `shouldBe`((no p \/ (q /\ no r)) \/ s)
    it "literal ej 1" $
      literal p
      `shouldBe` True
    it "literal ej 2" $
      literal (no p)
      `shouldBe` True
    it "literal ej 2" $
      literal (no (p --> q))
      `shouldBe` False
    it "complementario ej 1" $
      complementario p
      `shouldBe` no p
    it "complementario ej 2" $
      complementario (no p)
      `shouldBe` p
    it "interiorizaDisyuncion ej 1" $
      interiorizaDisyuncion (p \/ (q /\ r))
      `shouldBe` ((p \/ q) /\ (p \/ r))
    it "interiorizaDisyuncion ej 2" $
      interiorizaDisyuncion ((p /\ q) \/ r)
      `shouldBe` ((p \/ r) /\ (q \/ r))
    it "formaNormalConjuntiva ej 1" $
      formaNormalConjuntiva (p /\ (q --> r))
      `shouldBe` (p /\ (no q \/ r))
    it "formaNormalConjuntiva ej 2" $
      formaNormalConjuntiva (no (p /\ (q --> r)))
      `shouldBe` ((no p \/ q) /\ (no p \/ no r))
    it "formaNormalConjuntiva ej 3" $
      formaNormalConjuntiva (no(p <--> r))
      `shouldBe` (((p \/ r) /\ (p \/ no p)) /\ ((no r \/ r) /\ (no r \/ no p)))
    it "interiorizaConjuncion ej 1" $
      interiorizaConjuncion (p /\ (q \/ r))
      `shouldBe` ((p /\ q) \/ (p /\ r))
    it "interiorizaConjuncion ej 2" $
      interiorizaConjuncion ((p \/ q) /\ r)
      `shouldBe` ((p /\ r) \/ (q /\ r))
    it "formaNormalDisyuntiva ej 1" $
      formaNormalDisyuntiva (p /\ (q --> r))
      `shouldBe` ((p /\ no q) \/ (p /\ r))
    it "formaNormalDisyuntiva ej 2" $
      formaNormalDisyuntiva (no (p /\ (q --> r)))
      `shouldBe` (no p \/ (q /\ no r))
