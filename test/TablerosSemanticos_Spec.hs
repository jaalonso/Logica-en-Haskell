module TablerosSemanticos_Spec (main, spec) where

import SintaxisSemantica (
  (/\),
  (\/),
  (-->),
  (<-->),
  no,
  p,
  p1,
  p2,
  q,
  r,
  s,
  )
import TablerosSemanticos (
  componentes,
  conjuntoDeLiterales,
  conjuntoDeLiterales1,
  conjuntoDeLiterales2,
  dobleNegacion,
  esDeduciblePorTableros,
  esDeduciblePorTableros2,
  esTeoremaPorTableros,
  esTeoremaPorTableros2,
  expansionAlfa,
  expansionBeta,
  expansionDN,
  modelosGenerales,
  modelosTab,
  subconjunto,
  subconjunto2,
  subconjunto3,
  sucesores,
  sucesores1,
  tieneContradiccion,
  tieneContradiccion1,
  tieneContradiccion3,
  tieneContradiccion4,
  tieneContradiccion5,
  )
import Test.Hspec (
  Spec,
  describe,
  hspec,
  it,
  shouldBe
  )

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "dobleNegacion" $ do
    it "e1" $
      dobleNegacion (no (no p))     `shouldBe`  True
    it "e2" $
      dobleNegacion (no (p --> q))  `shouldBe`  False

  describe "componentes" $ do
    it "e1" $
      componentes (p /\ q --> r)       `shouldBe`  [no (p /\ q),r]
    it "e2" $
      componentes (no (p /\ q --> r))  `shouldBe`  [(p /\ q),no r]

  describe "conjuntoDeLiterales" $ do
    it "e1" $
      conjuntoDeLiterales1 [p --> q, no r, r /\ s, p]  `shouldBe`  False
    it "e2" $
      conjuntoDeLiterales1 [p, no q, r]                `shouldBe`  True
    it "e3" $
      conjuntoDeLiterales2 [p --> q, no r, r /\ s, p]  `shouldBe`  False
    it "e4" $
      conjuntoDeLiterales2 [p, no q, r]                `shouldBe`  True
    it "e5" $
      conjuntoDeLiterales [p --> q, no r, r /\ s, p]  `shouldBe`  False
    it "e6" $
      conjuntoDeLiterales [p, no q, r]                `shouldBe`  True

  describe "tieneContradiccion" $ do
    it "e1" $
      tieneContradiccion1 [r, p /\ q, s, no(p /\ q)]  `shouldBe`  True
    it "e2" $
      tieneContradiccion  [r, p /\ q, s, no(p /\ q)]  `shouldBe`  True
    it "e3" $
      tieneContradiccion3 [r, p /\ q, s, no(p /\ q)]  `shouldBe`  True
    it "e4" $
      tieneContradiccion4 [r, p /\ q, s, no(p /\ q)]  `shouldBe`  True
    it "e5" $
      tieneContradiccion5 [r, p /\ q, s, no(p /\ q)]  `shouldBe`  True

  describe "expansionDN" $
    it "e1" $
      expansionDN [p, no(no q), r] (no(no q))  `shouldBe`  [[q,p,r]]

  describe "expansionAlfa" $
    it "e1" $
      expansionAlfa [q, (p1 /\ p2) , r] (p1 /\ p2)  `shouldBe`  [[p1,p2,q,r]]

  describe "expansionBeta" $
    it "e1" $
      expansionBeta [q, (p1 \/ p2) , r] (p1 \/ p2)  `shouldBe`  [[p1,q,r],[p2,q,r]]

  describe "sucesores" $ do
    it "e1" $
      sucesores1 [q \/ s, no(no r), p1 /\ p2] `shouldBe` [[r,(q \/ s),(p1 /\ p2)]]
    it "e2" $
      sucesores1 [r,(q \/ s),(p1 /\ p2)]      `shouldBe` [[p1,p2,r,(q \/ s)]]
    it "e3" $
      sucesores1 [p1,p2,r,(q \/ s)]           `shouldBe` [[q,p1,p2,r],[s,p1,p2,r]]
    it "e4" $
      sucesores  [q \/ s, no(no r), p1 /\ p2] `shouldBe` [[r,(q \/ s),(p1 /\ p2)]]
    it "e5" $
      sucesores  [r,(q \/ s),(p1 /\ p2)]      `shouldBe` [[p1,p2,r,(q \/ s)]]
    it "e6" $
      sucesores  [p1,p2,r,(q \/ s)]           `shouldBe` [[q,p1,p2,r],[s,p1,p2,r]]

  describe "modelosTab" $ do
    it "e1" $
      modelosTab [p --> q, no(q --> p)]
      `shouldBe` [[no p,q],[q,no p]]
    it "e2" $
      modelosTab [p --> q, no q --> no p]
      `shouldBe` [[q,no p],[no p],[q],[no p,q]]

  describe "subconjunto" $ do
    it "e1" $
      subconjunto  [1,3] [3,2,1]    `shouldBe`  True
    it "e2" $
      subconjunto  [1,3,5] [3,2,1]  `shouldBe` False
    it "e3" $
      subconjunto2 [1,3] [3,2,1]    `shouldBe`  True
    it "e4" $
      subconjunto2 [1,3,5] [3,2,1]  `shouldBe` False
    it "e5" $
      subconjunto3 [1,3] [3,2,1]    `shouldBe`  True
    it "e6" $
      subconjunto3 [1,3,5] [3,2,1]  `shouldBe` False

  describe "modelosGenerales" $
    it "e1" $
      modelosGenerales [p --> q, no q --> no p]  `shouldBe`  [[no p],[q]]

  describe "esTeoremaPorTableros" $ do
    it "e1" $
      esTeoremaPorTableros  (p --> p)  `shouldBe`  True
    it "e2" $
      esTeoremaPorTableros  (p --> q)  `shouldBe`  False
    it "e3" $
      esTeoremaPorTableros2 (p --> p)  `shouldBe`  True
    it "e4" $
      esTeoremaPorTableros2 (p --> q)  `shouldBe`  False

  describe "esDeduciblePorTableros" $ do
    it "e1" $
      esDeduciblePorTableros  [p --> q, q --> r] (p --> r)   `shouldBe`  True
    it "e2" $
      esDeduciblePorTableros  [p --> q, q --> r] (p <--> r)  `shouldBe`  False
    it "e3" $
      esDeduciblePorTableros2 [p --> q, q --> r] (p --> r)   `shouldBe`  True
    it "e4" $
      esDeduciblePorTableros2 [p --> q, q --> r] (p <--> r)  `shouldBe`  False
