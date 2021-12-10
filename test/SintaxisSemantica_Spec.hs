module SintaxisSemantica_Spec (main, spec) where

import SintaxisSemantica
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "SintaxisSemantica" $ do
    it "simbolosPropForm ej 1" $
      simbolosPropForm (p /\ q --> p)
      `shouldBe` [p,q]
    it "significado ej 1" $
      significado ((p \/ q) /\ ((no q) \/ r)) [r]
      `shouldBe` False
    it "significado ej 2" $
      significado ((p \/ q) /\ ((no q) \/ r)) [p,r]
      `shouldBe` True
    it "interpretacionesForm ej 1" $
      interpretacionesForm (p /\ q --> p)
      `shouldBe` [[p,q],[p],[q],[]]
    it "esModeloFormula ej 1" $
      esModeloFormula [r]   ((p \/ q) /\ ((no q) \/ r))
      `shouldBe` False
    it "esModeloFormula ej 2" $
      esModeloFormula [p,r] ((p \/ q) /\ ((no q) \/ r))
      `shouldBe` True
    it "modelosFormula ej 1" $
      modelosFormula ((p \/ q) /\ ((no q) \/ r))
      `shouldBe` [[p,q,r],[p,r],[p],[q,r]]
    it "esValida ej 1" $
      esValida (p --> p)
      `shouldBe` True
    it "esValida ej 2" $
      esValida (p --> q)
      `shouldBe` False
    it "esValida ej 3" $
      esValida ((p --> q) \/ (q --> p))
      `shouldBe` True
    it "esInsatisfacible ej 1" $
      esInsatisfacible (p /\ (no p))
      `shouldBe` True
    it "esInsatisfacible ej 2" $
      esInsatisfacible ((p --> q) /\ (q --> r))
      `shouldBe` False
    it "esSatisfacible ej 1" $
      esSatisfacible (p /\ (no p))
      `shouldBe` False
    it "esSatisfacible ej 2" $
      esSatisfacible ((p --> q) /\ (q --> r))
      `shouldBe` True
    it "unionGeneral ej 1" $
      unionGeneral [[1]]
      `shouldBe` [1]
    it "unionGeneral ej 2" $
      unionGeneral [[1],[1,2],[2,3]]
      `shouldBe` [1,2,3]
    it "simbolosPropConj ej 1" $
      simbolosPropConj [p /\ q --> r, p --> s]
      `shouldBe` [p,q,r,s]
    it "interpretacionesConjunto ej 1" $
      interpretacionesConjunto [p --> q, q --> r]
      `shouldBe` [[p,q,r],[p,q],[p,r],[p],[q,r],[q],[r],[]]
    it "esModeloConjunto ej 1" $
      esModeloConjunto [p,r] [(p \/ q) /\ ((no q) \/ r), q --> r]
      `shouldBe` True
    it "esModeloConjunto ej 2" $
      esModeloConjunto [p,r] [(p \/ q) /\ ((no q) \/ r), r --> q]
      `shouldBe` False
    it "modelosConjunto ej 1" $
      modelosConjunto [(p \/ q) /\ ((no q) \/ r), q --> r]
      `shouldBe` [[p,q,r],[p,r],[p],[q,r]]
    it "modelosConjunto ej 2" $
      modelosConjunto [(p \/ q) /\ ((no q) \/ r), r --> q]
      `shouldBe` [[p,q,r],[p],[q,r]]
    it "esConsistente ej 1" $
      esConsistente [(p \/ q) /\ ((no q) \/ r), p --> r]
      `shouldBe` True
    it "esConsistente ej 2" $
      esConsistente [(p \/ q) /\ ((no q) \/ r), p --> r, no r]
      `shouldBe` False
    it "esInconsistente ej 1" $
      esInconsistente [(p \/ q) /\ ((no q) \/ r), p --> r]
      `shouldBe` False
    it "esInconsistente ej 2" $
      esInconsistente [(p \/ q) /\ ((no q) \/ r), p --> r, no r]
      `shouldBe` True
    it "esConsecuencia ej 1" $
      esConsecuencia [p --> q, q --> r] (p --> r)
      `shouldBe` True
    it "esConsecuencia ej 2" $
      esConsecuencia [p] (p /\ q)
      `shouldBe` False
