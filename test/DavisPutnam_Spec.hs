module DavisPutnam_Spec (main, spec) where

import SintaxisSemantica
import DavisPutnam
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "esTautologia" $ do
    it "e1" $
      esTautologia  [p, q, no p]  `shouldBe`  True
    it "e2" $
      esTautologia  [p, q, no r]  `shouldBe`  False
    it "e3" $
      esTautologia  []            `shouldBe`  False
    it "e4" $
      esTautologia2 [p, q, no p]  `shouldBe`  True
    it "e5" $
      esTautologia2 [p, q, no r]  `shouldBe`  False
    it "e6" $
      esTautologia2 []            `shouldBe`  False
    it "e7" $
      esTautologia3 [p, q, no p]  `shouldBe`  True
    it "e8" $
      esTautologia3 [p, q, no r]  `shouldBe`  False
    it "e9" $
      esTautologia3 []            `shouldBe`  False
    it "e10" $
      esTautologia4 [p, q, no p]  `shouldBe`  True
    it "e11" $
      esTautologia4 [p, q, no r]  `shouldBe`  False
    it "e12" $
      esTautologia4 []            `shouldBe`  False
    it "e13" $
      esTautologia5 [p, q, no p]  `shouldBe`  True
    it "e14" $
      esTautologia5 [p, q, no r]  `shouldBe`  False
    it "e15" $
      esTautologia5 []            `shouldBe`  False

  describe "eliminaTautologias" $ do
    it "e1" $
      eliminaTautologias  [[p, q], [p, q, no p]]  `shouldBe`  [[p,q]]
    it "e2" $
      eliminaTautologias2 [[p, q], [p, q, no p]]  `shouldBe`  [[p,q]]

  describe "esUnitaria" $ do
    it "e1" $
      esUnitaria [p]     `shouldBe`  True
    it "e2" $
      esUnitaria [no p]  `shouldBe`  True
    it "e3" $
      esUnitaria [p, q]  `shouldBe`  False

  describe "eliminaClausulaUnitaria" $ do
    it "e1" $
      eliminaClausulaUnitaria (no p) [[p,q,no r],[p,no q],[no p],[r]]
      `shouldBe` [[q,no r],[no q],[r]]
    it "e2" $
      eliminaClausulaUnitaria (no q) [[q,no r],[no q],[r]]
      `shouldBe` [[no r],[r]]
    it "e3" $
      eliminaClausulaUnitaria (no r) [[no r],[r],[p]]
      `shouldBe` [[],[p]]

  describe "clausulaUnitaria" $ do
    it "e1" $
      clausulaUnitaria [[p,q],[p],[no q]]  `shouldBe`  Just p
    it "e2" $
      clausulaUnitaria [[p,q],[p,no q]]    `shouldBe`  Nothing

  describe "eliminaClausulasUnitarias" $ do
    it "e1" $
      eliminaClausulasUnitarias [[p,q,no r],[p,no q],[no p],[r],[u]]
      `shouldBe` [[],[u]]
    it "e2" $
      eliminaClausulasUnitarias [[p,q],[no q],[no p,q,no r]]
      `shouldBe` []
    it "e3" $
      eliminaClausulasUnitarias [[no p,q],[p],[r,u]]
      `shouldBe` [[r,u]]

  describe "literales" $
    it "e1" $
      literales [[p,q],[p,q,no p]]  `shouldBe`  [p,q,no p]

  describe "esLiteralPuro" $ do
    it "e1" $
      esLiteralPuro p [[p,q],[p,no q],[r,q],[r,no q]]  `shouldBe`  True
    it "e2" $
      esLiteralPuro q [[p,q],[p,no q],[r,q],[r,no q]]  `shouldBe`  False

  describe "eliminaLiteralPuro" $ do
    it "e1" $
      eliminaLiteralPuro p [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` [[r,q],[r,no q]]
    it "e2" $
      eliminaLiteralPuro r [[r,q],[r,no q]]
      `shouldBe` []
    it "e3" $
      eliminaLiteralPuro2 p [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` [[r,q],[r,no q]]
    it "e4" $
      eliminaLiteralPuro2 r [[r,q],[r,no q]]
      `shouldBe` []

  describe "literalesPuros" $
    it "e1" $
      literalesPuros [[p,q],[p,no q],[r,q],[r,no q]]  `shouldBe`  [p,r]

  describe "eliminaLiteralesPuros" $ do
    it "e1" $
      eliminaLiteralesPuros [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` []
    it "e12" $
      eliminaLiteralesPuros [[p,q],[r,no s],[no r,s]]
      `shouldBe` [[r,no s],[no r,s]]

  describe "bifurcacion" $
    it "e1" $
      bifurcacion [[p,no q],[no p,q],[q,no r],[no q,no r]] p
      `shouldBe` ([[no q],[q,no r],[no q,no r]],[[q],[q,no r],[no q,no r]])

  describe "tieneClausulasUnitarias" $ do
    it "e1" $
      tieneClausulasUnitarias [[p,q],[p],[no q]]  `shouldBe`  True
    it "e2" $
      tieneClausulasUnitarias [[p,q],[p,no q]]    `shouldBe`  False

  describe "tieneLiteralesPuros" $ do
    it "e1" $
      tieneLiteralesPuros [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` True
    it "e2" $
      tieneLiteralesPuros [[p,q],[no p,no q],[no r,q],[r,no q]]
      `shouldBe` False

  describe "esInconsistentePorDP" $ do
    it "e1" $
      esInconsistentePorDP [[p,q],[p,q,no p]]
      `shouldBe` False
    it "e2" $
      esInconsistentePorDP [[p,q,no r],[p,no q],[no p],[r],[u]]
      `shouldBe` True
    it "e3" $
      esInconsistentePorDP [[p,q],[no q],[no p,q,no r]]
      `shouldBe` False
    it "e4" $
      esInconsistentePorDP [[no p,q],[p],[r,u]]
      `shouldBe` False
    it "e5" $
      esInconsistentePorDP [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` False
    it "e6" $
      esInconsistentePorDP [[p,q],[r,no s],[no r,s]]
      `shouldBe` False
    it "e7" $
      esInconsistentePorDP [[p,no q],[no p,q],[q,no r],[no q,no r]]
      `shouldBe` False
    it "e8" $
      esInconsistentePorDP [[p,q],[p,no q],[r,q],[r,no q]]
      `shouldBe` False

  describe "esValidaPorDP" $ do
    it "e1" $
      esValidaPorDP (p --> p)                 `shouldBe`  True
    it "e2" $
      esValidaPorDP ((p --> q) \/ (q --> p))  `shouldBe`  True
    it "e3" $
      esValidaPorDP (p --> q)                 `shouldBe`  False

  describe "esConsecuenciaPorDP" $ do
    it "e1" $
      esConsecuenciaPorDP [p --> q, q --> r] (p --> r)  `shouldBe`  True
    it "e2" $
      esConsecuenciaPorDP [p] (p /\ q)  `shouldBe`  False
