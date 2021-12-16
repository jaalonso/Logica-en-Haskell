module Clausulas_Spec (main, spec) where

import SintaxisSemantica (
  (\/),
  (/\),
  (-->),
  (<-->),
  no,
  p,
  q,
  r)
import Clausulas (
  clausula,
  clausulas,
  clausulas1,
  clausulasConjunto,
  clausulasConjunto1,
  clausulasConjunto2,
  clausulasFNC,
  esClausulaInsatisfacible,
  esClausulaInsatisfacible1,
  esClausulaInsatisfacible3,
  esClausulaInsatisfacible4,
  esClausulaInsatisfacible5,
  esClausulaSatisfacible,
  esClausulaSatisfacible1,
  esClausulaSatisfacible3,
  esClausulaSatisfacible4,
  esClausulaSatisfacible5,
  esClausulaValida,
  esClausulaValida1,
  esClausulaValida2,
  esClausulaValida3,
  esClausulaValida4,
  esClausulaValida5,
  esConjuntoConsistenteDeClausulas,
  esConjuntoConsistenteDeClausulas1,
  esConjuntoInconsistenteDeClausulas,
  esConjuntoInconsistenteDeClausulas1,
  esConjuntoValidoDeClausulas,
  esConjuntoValidoDeClausulas1,
  esConjuntoValidoDeClausulas2,
  esConjuntoValidoDeClausulas4,
  esConjuntoValidoDeClausulas5,
  esConsecuenciaEntreClausulas,
  esConsecuenciaPorClausulas,
  esConsecuenciaPorClausulas2,
  esConsecuenciaPorClausulas3,
  esModeloClausula,
  esModeloClausula1,
  esModeloClausula2,
  esModeloConjuntoClausulas,
  esModeloConjuntoClausulas1,
  esModeloConjuntoClausulas2,
  esModeloLiteral,
  esValidaPorClausulas,
  esValidaPorClausulas1,
  interpretacionesClausula,
  interpretacionesClausula1,
  interpretacionesConjuntoClausula,
  interpretacionesConjuntoClausula1,
  simbolosProposicionalesClausula,
  modelosClausula,
  modelosClausula1,
  modelosClausula2,
  modelosConjuntoClausulas,
  modelosConjuntoClausulas1,
  modelosConjuntoClausulas2,
  simbolosProposicionalesClausula1,
  simbolosProposicionalesConjuntoClausula,
  simbolosProposicionalesConjuntoClausula1
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
  describe "clausula" $ do
    it "e1" $
      clausula p                                 `shouldBe`  [p]
    it "e2" $
      clausula (no p)                            `shouldBe`  [no p]
    it "e3" $
      clausula (((no p) \/ r) \/ ((no p) \/ q))  `shouldBe`  [q,r,no p]

  describe "clausulasFNC" $ do
    it "e1" $
      clausulasFNC (p /\ ((no q) \/ r))
      `shouldBe` [[p],[r, no q]]
    it "e2" $
      clausulasFNC (((no p) \/ q) /\ ((no p) \/ (no r)))
      `shouldBe` [[q, no p],[no p,no r]]

  describe "clausulas" $ do
    it "e1" $
      clausulas (p /\ (q --> r))
      `shouldBe` [[p],[r,no q]]
    it "e2" $
      clausulas (no (p /\ (q --> r)))
      `shouldBe` [[q,no p],[no p,no r]]
    it "e3" $
      clausulas (no(p <--> r))
      `shouldBe` [[p,r],[p,no p],[r,no r],[no p,no r]]
    it "e4" $
      clausulas1 (p /\ (q --> r))
      `shouldBe` [[p],[r,no q]]
    it "e5" $
      clausulas1 (no (p /\ (q --> r)))
      `shouldBe` [[q,no p],[no p,no r]]
    it "e6" $
      clausulas1 (no(p <--> r))
      `shouldBe` [[p,r],[p,no p],[r,no r],[no p,no r]]

  describe "clausulasConjunto" $ do
    it "e1" $
      clausulasConjunto [p --> q, q --> r]   `shouldBe`  [[q,no p],[r,no q]]
    it "e2" $
      clausulasConjunto [p --> q, q <--> p]  `shouldBe`  [[q,no p],[p,no q]]
    it "e3" $
      clausulasConjunto1 [p --> q, q --> r]   `shouldBe`  [[q,no p],[r,no q]]
    it "e4" $
      clausulasConjunto1 [p --> q, q <--> p]  `shouldBe`  [[q,no p],[p,no q]]
    it "e5" $
      clausulasConjunto2 [p --> q, q --> r]   `shouldBe`  [[q,no p],[r,no q]]
    it "e6" $
      clausulasConjunto2 [p --> q, q <--> p]  `shouldBe`  [[q,no p],[p,no q]]

  describe "simbolosProposicionalesClausula" $ do
    it "e1" $
      simbolosProposicionalesClausula [p, q, no p]  `shouldBe`  [p,q]
    it "e2" $
      simbolosProposicionalesClausula1 [p, q, no p]  `shouldBe`  [p,q]

  describe "simbolosProposicionalesConjuntoClausula" $ do
    it "e1" $
      simbolosProposicionalesConjuntoClausula [[p, q],[no q, r]]
      `shouldBe` [p,q,r]
    it "e2" $
      simbolosProposicionalesConjuntoClausula1 [[p, q],[no q, r]]
      `shouldBe` [p,q,r]
    it "e3" $
      simbolosProposicionalesConjuntoClausula1 [[p, q],[no q, r]]
      `shouldBe` [p,q,r]

  describe "interpretacionesClausula" $ do
    it "e1" $
      interpretacionesClausula [p, q, no p]  `shouldBe`  [[p,q],[p],[q],[]]
    it "e2" $
      interpretacionesClausula []            `shouldBe`  [[]]
    it "e3" $
      interpretacionesClausula1 [p, q, no p]  `shouldBe`  [[p,q],[p],[q],[]]
    it "e4" $
      interpretacionesClausula1 []            `shouldBe`  [[]]

  describe "interpretacionesConjuntoClausula" $ do
    it "e1" $
      interpretacionesConjuntoClausula [[p, no q],[no p, q]]
      `shouldBe` [[p,q],[p],[q],[]]
    it "e2" $
      interpretacionesConjuntoClausula []
      `shouldBe` [[]]
    it "e3" $
      interpretacionesConjuntoClausula1 [[p, no q],[no p, q]]
      `shouldBe` [[p,q],[p],[q],[]]
    it "e4" $
      interpretacionesConjuntoClausula1 []
      `shouldBe` [[]]

  describe "esModeloLiteral" $ do
    it "e1" $
      esModeloLiteral [p,r] p       `shouldBe`  True
    it "e2" $
      esModeloLiteral [p,r] q       `shouldBe`  False
    it "e3" $
      esModeloLiteral [p,r] (no p)  `shouldBe`  False
    it "e4" $
      esModeloLiteral [p,r] (no q)  `shouldBe`  True

  describe "esModeloClausula" $ do
    it "e1" $
      esModeloClausula [p,r] [p, q]     `shouldBe`  True
    it "e2" $
      esModeloClausula [r] [p, no q]    `shouldBe`  True
    it "e3" $
      esModeloClausula [q,r] [p, no q]  `shouldBe`  False
    it "e4" $
      esModeloClausula [q,r] []         `shouldBe`  False
    it "e5" $
      esModeloClausula1 [p,r] [p, q]     `shouldBe`  True
    it "e6" $
      esModeloClausula1 [r] [p, no q]    `shouldBe`  True
    it "e7" $
      esModeloClausula1 [q,r] [p, no q]  `shouldBe`  False
    it "e8" $
      esModeloClausula1 [q,r] []         `shouldBe`  False
    it "e9" $
      esModeloClausula2 [p,r] [p, q]     `shouldBe`  True
    it "e10" $
      esModeloClausula2 [r] [p, no q]    `shouldBe`  True
    it "e11" $
      esModeloClausula2 [q,r] [p, no q]  `shouldBe`  False
    it "e12" $
      esModeloClausula2 [q,r] []         `shouldBe`  False

  describe "modelosClausula" $ do
    it "e1" $
      modelosClausula [no p, q]  `shouldBe`  [[p,q],[q],[]]
    it "e2" $
      modelosClausula [no p, p]  `shouldBe`  [[p],[]]
    it "e3" $
      modelosClausula []         `shouldBe`  []
    it "e4" $
      modelosClausula1 [no p, q]  `shouldBe`  [[p,q],[q],[]]
    it "e5" $
      modelosClausula1 [no p, p]  `shouldBe`  [[p],[]]
    it "e6" $
      modelosClausula1 []         `shouldBe`  []
    it "e7" $
      modelosClausula2 [no p, q]  `shouldBe`  [[p,q],[q],[]]
    it "e8" $
      modelosClausula2 [no p, p]  `shouldBe`  [[p],[]]
    it "e9" $
      modelosClausula2 []         `shouldBe`  []

  describe "esModeloConjuntoClausulas" $ do
    it "e1" $
      esModeloConjuntoClausulas [p,r] [[p, no q], [r]]  `shouldBe`  True
    it "e2" $
      esModeloConjuntoClausulas [p] [[p, no q], [r]]    `shouldBe`  False
    it "e3" $
      esModeloConjuntoClausulas [p] []                  `shouldBe`  True
    it "e4" $
      esModeloConjuntoClausulas1 [p,r] [[p, no q], [r]]  `shouldBe`  True
    it "e5" $
      esModeloConjuntoClausulas1 [p] [[p, no q], [r]]    `shouldBe`  False
    it "e6" $
      esModeloConjuntoClausulas1 [p] []                  `shouldBe`  True
    it "e7" $
      esModeloConjuntoClausulas2 [p,r] [[p, no q], [r]]  `shouldBe`  True
    it "e8" $
      esModeloConjuntoClausulas2 [p] [[p, no q], [r]]    `shouldBe`  False
    it "e9" $
      esModeloConjuntoClausulas2 [p] []                  `shouldBe`  True

  describe "modelosConjuntoClausulas" $ do
    it "e1" $
      modelosConjuntoClausulas [[no p, q], [no q, p]]
      `shouldBe` [[p,q],[]]
    it "e2" $
      modelosConjuntoClausulas [[no p, q], [p], [no q]]
      `shouldBe` []
    it "e3" $
      modelosConjuntoClausulas [[p, no p, q]]
      `shouldBe` [[p,q],[p],[q],[]]
    it "e4" $
      modelosConjuntoClausulas1 [[no p, q], [no q, p]]
      `shouldBe` [[p,q],[]]
    it "e5" $
      modelosConjuntoClausulas1 [[no p, q], [p], [no q]]
      `shouldBe` []
    it "e6" $
      modelosConjuntoClausulas1 [[p, no p, q]]
      `shouldBe` [[p,q],[p],[q],[]]
    it "e7" $
      modelosConjuntoClausulas2 [[no p, q], [no q, p]]
      `shouldBe` [[p,q],[]]
    it "e8" $
      modelosConjuntoClausulas2 [[no p, q], [p], [no q]]
      `shouldBe` []
    it "e9" $
      modelosConjuntoClausulas2 [[p, no p, q]]
      `shouldBe` [[p,q],[p],[q],[]]

  describe "esClausulaValida" $ do
    it "e1" $
      esClausulaValida [p, q, no p]  `shouldBe`  True
    it "e2" $
      esClausulaValida [p, q, no r]  `shouldBe`  False
    it "e3" $
      esClausulaValida []            `shouldBe`  False
    it "e4" $
      esClausulaValida1 [p, q, no p]  `shouldBe`  True
    it "e5" $
      esClausulaValida1 [p, q, no r]  `shouldBe`  False
    it "e6" $
      esClausulaValida1 []            `shouldBe`  False
    it "e7" $
      esClausulaValida2 [p, q, no p]  `shouldBe`  True
    it "e8" $
      esClausulaValida2 [p, q, no r]  `shouldBe`  False
    it "e9" $
      esClausulaValida2 []            `shouldBe`  False
    it "e10" $
      esClausulaValida3 [p, q, no p]  `shouldBe`  True
    it "e11" $
      esClausulaValida3 [p, q, no r]  `shouldBe`  False
    it "e12" $
      esClausulaValida3 []            `shouldBe`  False
    it "e13" $
      esClausulaValida4 [p, q, no p]  `shouldBe`  True
    it "e14" $
      esClausulaValida4 [p, q, no r]  `shouldBe`  False
    it "e15" $
      esClausulaValida4 []            `shouldBe`  False
    it "e16" $
      esClausulaValida5 [p, q, no p]  `shouldBe`  True
    it "e17" $
      esClausulaValida5 [p, q, no r]  `shouldBe`  False
    it "e18" $
      esClausulaValida5 []            `shouldBe`  False

  describe "esClausulaInsatisfacible" $ do
    it "e1" $
      esClausulaInsatisfacible [p, q, no p]  `shouldBe`  False
    it "e2" $
      esClausulaInsatisfacible [p, q, no r]  `shouldBe`  False
    it "e3" $
      esClausulaInsatisfacible []            `shouldBe`  True
    it "e4" $
      esClausulaInsatisfacible1 [p, q, no p]  `shouldBe`  False
    it "e5" $
      esClausulaInsatisfacible1 [p, q, no r]  `shouldBe`  False
    it "e6" $
      esClausulaInsatisfacible1 []            `shouldBe`  True
    it "e7" $
      esClausulaInsatisfacible3 [p, q, no p]  `shouldBe`  False
    it "e8" $
      esClausulaInsatisfacible3 [p, q, no r]  `shouldBe`  False
    it "e9" $
      esClausulaInsatisfacible3 []            `shouldBe`  True
    it "e10" $
      esClausulaInsatisfacible4 [p, q, no p]  `shouldBe`  False
    it "e11" $
      esClausulaInsatisfacible4 [p, q, no r]  `shouldBe`  False
    it "e12" $
      esClausulaInsatisfacible4 []            `shouldBe`  True
    it "e13" $
      esClausulaInsatisfacible5 [p, q, no p]  `shouldBe`  False
    it "e14" $
      esClausulaInsatisfacible5 [p, q, no r]  `shouldBe`  False
    it "e15" $
      esClausulaInsatisfacible5 []            `shouldBe`  True

  describe "esClausulaSatisfacible" $ do
    it "e1" $
      esClausulaSatisfacible [p, q, no p]  `shouldBe`  True
    it "e2" $
      esClausulaSatisfacible [p, q, no r]  `shouldBe`  True
    it "e3" $
      esClausulaSatisfacible []  `shouldBe`  False
    it "e4" $
      esClausulaSatisfacible1 [p, q, no p]  `shouldBe`  True
    it "e5" $
      esClausulaSatisfacible1 [p, q, no r]  `shouldBe`  True
    it "e6" $
      esClausulaSatisfacible1 []  `shouldBe`  False
    it "e7" $
      esClausulaSatisfacible3 [p, q, no p]  `shouldBe`  True
    it "e8" $
      esClausulaSatisfacible3 [p, q, no r]  `shouldBe`  True
    it "e9" $
      esClausulaSatisfacible3 []  `shouldBe`  False
    it "e10" $
      esClausulaSatisfacible4 [p, q, no p]  `shouldBe`  True
    it "e11" $
      esClausulaSatisfacible4 [p, q, no r]  `shouldBe`  True
    it "e12" $
      esClausulaSatisfacible4 []  `shouldBe`  False
    it "e13" $
      esClausulaSatisfacible5 [p, q, no p]  `shouldBe`  True
    it "e14" $
      esClausulaSatisfacible5 [p, q, no r]  `shouldBe`  True
    it "e15" $
      esClausulaSatisfacible5 []  `shouldBe`  False

  describe "esConjuntoValidoDeClausulas" $ do
    it "e1" $
      esConjuntoValidoDeClausulas [[no p, q], [no q, p]]  `shouldBe`  False
    it "e2" $
      esConjuntoValidoDeClausulas [[no p, p], [no q, q]]  `shouldBe`  True
    it "e3" $
      esConjuntoValidoDeClausulas []                      `shouldBe`  True
    it "e4" $
      esConjuntoValidoDeClausulas1 [[no p, q], [no q, p]]  `shouldBe`  False
    it "e5" $
      esConjuntoValidoDeClausulas1 [[no p, p], [no q, q]]  `shouldBe`  True
    it "e6" $
      esConjuntoValidoDeClausulas1 []                      `shouldBe`  True
    it "e7" $
      esConjuntoValidoDeClausulas2 [[no p, q], [no q, p]]  `shouldBe`  False
    it "e8" $
      esConjuntoValidoDeClausulas2 [[no p, p], [no q, q]]  `shouldBe`  True
    it "e9" $
      esConjuntoValidoDeClausulas2 []                      `shouldBe`  True
    it "e10" $
      esConjuntoValidoDeClausulas4 [[no p, q], [no q, p]]  `shouldBe`  False
    it "e11" $
      esConjuntoValidoDeClausulas4 [[no p, p], [no q, q]]  `shouldBe`  True
    it "e12" $
      esConjuntoValidoDeClausulas4 []                      `shouldBe`  True
    it "e13" $
      esConjuntoValidoDeClausulas5 [[no p, q], [no q, p]]  `shouldBe`  False
    it "e14" $
      esConjuntoValidoDeClausulas5 [[no p, p], [no q, q]]  `shouldBe`  True
    it "e15" $
      esConjuntoValidoDeClausulas5 []                      `shouldBe`  True

  describe "esConjuntoConsistenteDeClausulas" $ do
    it "e1" $
      esConjuntoConsistenteDeClausulas [[no p, q], [no q, p]]  `shouldBe`  True
    it "e2" $
      esConjuntoConsistenteDeClausulas [[no p, p], [no q, q]]  `shouldBe`  True
    it "e3" $
      esConjuntoConsistenteDeClausulas []                      `shouldBe`  True
    it "e4" $
      esConjuntoConsistenteDeClausulas1 [[no p, q], [no q, p]]  `shouldBe`  True
    it "e5" $
      esConjuntoConsistenteDeClausulas1 [[no p, p], [no q, q]]  `shouldBe`  True
    it "e6" $
      esConjuntoConsistenteDeClausulas1 []                      `shouldBe`  True

  describe "esConjuntoInconsistenteDeClausulas" $ do
    it "e1" $
      esConjuntoInconsistenteDeClausulas [[no p,q],[no q,p]]  `shouldBe`  False
    it "e2" $
      esConjuntoInconsistenteDeClausulas [[no p],[p]]         `shouldBe`  True
    it "e3" $
      esConjuntoInconsistenteDeClausulas1 [[no p,q],[no q,p]]  `shouldBe`  False
    it "e4" $
      esConjuntoInconsistenteDeClausulas1 [[no p],[p]]         `shouldBe`  True

  describe "esValidaPorClausulas" $ do
    it "e1" $
      esValidaPorClausulas (p --> q)                 `shouldBe`  False
    it "e2" $
      esValidaPorClausulas (p --> p)                 `shouldBe`  True
    it "e3" $
      esValidaPorClausulas ((p --> q) \/ (q --> p))  `shouldBe`  True
    it "e4" $
      esValidaPorClausulas1 (p --> q)                 `shouldBe`  False
    it "e5" $
      esValidaPorClausulas1 (p --> p)                 `shouldBe`  True
    it "e6" $
      esValidaPorClausulas1 ((p --> q) \/ (q --> p))  `shouldBe`  True

  describe "esConsecuenciaEntreClausulas" $ do
    it "e1" $
      esConsecuenciaEntreClausulas [[no p,q],[no q,r]] [[no p,r]]
      `shouldBe` True
    it "e2" $
      esConsecuenciaEntreClausulas [[p]] [[p],[q]]
      `shouldBe` False

  describe "esConsecuenciaPorClausulas" $ do
    it "e1" $
      esConsecuenciaPorClausulas [(p --> q), (q --> r)] (p --> r)
      `shouldBe` True
    it "e2" $
      esConsecuenciaPorClausulas [p] (p /\ q)
      `shouldBe` False
    it "e3" $
      esConsecuenciaPorClausulas2 [(p --> q), (q --> r)] (p --> r)
      `shouldBe` True
    it "e4" $
      esConsecuenciaPorClausulas2 [p] (p /\ q)
      `shouldBe` False
    it "e5" $
      esConsecuenciaPorClausulas3 [(p --> q), (q --> r)] (p --> r)
      `shouldBe` True
    it "e6" $
      esConsecuenciaPorClausulas3 [p] (p /\ q)
      `shouldBe` False
