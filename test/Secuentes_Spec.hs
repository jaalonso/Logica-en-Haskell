module Secuentes_Spec (main, spec) where

import SintaxisSemantica
import Secuentes
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "esAxioma" $ do
    it "e1" $
      esAxioma ([p /\ q, r], [r --> q, p /\ q])  `shouldBe`  True
    it "e2" $
      esAxioma ([p /\ q, r], [r --> q, p, q])    `shouldBe`  False

  describe "reglaIzquierda" $ do
    it "e1" $
      reglaIzquierda (no p) ([no p, q],[r])
      `shouldBe` [([q],[p,r])]
    it "e2" $
      reglaIzquierda (p /\ q) ([r, p /\ q],[s])
      `shouldBe` [([p,q,r],[s])]
    it "e3" $
      reglaIzquierda (p \/ q) ([r, p \/ q],[s])
      `shouldBe` [([p,r],[s]),([q,r],[s])]
    it "e4" $
      reglaIzquierda (p --> q) ([r, p --> q],[s])
      `shouldBe` [([r],[p,s]),([q,r],[s])]
    it "e5" $
      reglaIzquierda (p <--> q) ([r, p <--> q],[s])
      `shouldBe` [([p,q,r],[s]),([r],[p,q,s])]

  describe "reglaDerecha" $ do
    it "e1" $
      reglaDerecha (no p) ([q],[no p, r])
      `shouldBe` [([p,q],[r])]
    it "e2" $
      reglaDerecha (p /\ q) ([s],[p /\ q, r])
      `shouldBe` [([s],[p,r]),([s],[q,r])]
    it "e3" $
      reglaDerecha (p \/ q) ([s],[p \/ q, r])
      `shouldBe` [([s],[p,q,r])]
    it "e4" $
      reglaDerecha (p --> q) ([s],[p --> q, r])
      `shouldBe` [([p,s],[q,r])]
    it "e5" $
      reglaDerecha (p <--> q) ([s],[p <--> q, r])
      `shouldBe` [([p,s],[q,r]),([q,s],[p,r])]

  describe "esAtomica" $ do
    it "e1" $
      esAtomica p         `shouldBe`  True
    it "e2" $
      esAtomica (p /\ q)  `shouldBe`  False

  describe "compuestasIzquierda" $ do
    it "e1" $
      compuestasIzquierda  ([no p, q, r /\ s],[no q]) `shouldBe` [no p,(r /\ s)]
    it "e2" $
      compuestasIzquierda2 ([no p, q, r /\ s],[no q]) `shouldBe` [no p,(r /\ s)]
    it "e3" $
      compuestasIzquierda3 ([no p, q, r /\ s],[no q]) `shouldBe` [no p,(r /\ s)]

  describe "compuestasDerecha" $ do
    it "e1" $
      compuestasDerecha  ([no p, q, r /\ s],[no q, s --> p, r]) `shouldBe` [no q,(s --> p)]
    it "e2" $
      compuestasDerecha2 ([no p, q, r /\ s],[no q, s --> p, r]) `shouldBe` [no q,(s --> p)]
    it "e3" $
      compuestasDerecha3 ([no p, q, r /\ s],[no q, s --> p, r]) `shouldBe` [no q,(s --> p)]

  describe "esProbablePorSecuentes'" $ do
    it "e1" $
      esProbablePorSecuentes' ([p --> q, q --> r],[p --> r])   `shouldBe`  True
    it "e2" $
      esProbablePorSecuentes' ([p --> q, q --> r],[p <--> r])  `shouldBe`  False
    it "e3" $
      esProbablePorSecuentes' ([],[p --> p])                   `shouldBe`  True
    it "e4" $
      esProbablePorSecuentes' ([p /\ no(p)],[])                `shouldBe`  True

  describe "sonProbalesPorSecuentes" $
    it "e1" $
      sonProbalesPorSecuentes [([],[q,p,(p --> r)]),([r],[p,(p --> r)])]
      `shouldBe` True

  describe "sonProbalesPorSecuentes" $ do
    it "e1" $
      sonProbalesPorSecuentes [([],[q,p,(p --> r)]),([r],[p,(p --> r)])]
      `shouldBe` True
    it "e2" $
      sonProbalesPorSecuentes2 [([],[q,p,(p --> r)]),([r],[p,(p --> r)])]
      `shouldBe` True

  describe "esProbablePorSecuentes" $ do
    it "e1" $
      esProbablePorSecuentes ((p --> q) \/ (q --> p))  `shouldBe`  True
    it "e2" $
      esProbablePorSecuentes (p --> q)                 `shouldBe`  False

  describe "marcas" $
    it "e1" $
      marcas 3 `shouldBe` " ||| "

  describe "esDeduciblePorSecuentes" $ do
    it "e1" $
      esDeduciblePorSecuentes [p --> q, q --> r] (p --> r)
      `shouldBe` True
    it "e2" $
      esDeduciblePorSecuentes [p --> q, q --> r] (p <--> r)
      `shouldBe` False
