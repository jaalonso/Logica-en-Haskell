-- Clausulas.hs
-- Cláusulas.
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module Clausulas where

-- ---------------------------------------------------------------------
-- § Introducción                                                     --
-- ---------------------------------------------------------------------

-- En este módulo se implementa la sinstaxis y la semántica de las
-- cláusulas proposicionales siguiendo su exposición en el tema 5 de la
-- asignatura de "Lógica informática" que se encuentra en
-- https://bit.ly/3q9bl2J

-- ---------------------------------------------------------------------
-- Librería auxiliares                                                --
-- ---------------------------------------------------------------------

import SintaxisSemantica (
  Interpretacion,
  Prop(..),
  (\/),
  (/\),
  (-->),
  (<-->),
  no,
  p,
  q,
  r,
  simbolosPropConj,
  subconjuntos,
  unionGeneral
  )
import FormasNormales (
  Literal,
  complementario,
  formaNormalConjuntiva,
  literal)
import Data.List (sort, union)

-- ---------------------------------------------------------------------
-- § Cláusulas                                                          --
-- ---------------------------------------------------------------------

-- Nota: En los ejemplos se usará la notación de fórmulas del módulo
-- SintaxisSemantica. Por ejemplo,
ejFormula :: Prop
ejFormula = p --> q /\ (r <--> no p \/ q)

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir el tipo de datos Clausula como una lista de
-- literales.
-- ---------------------------------------------------------------------

type Clausula = [Literal]

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir la función
--    clausula :: Prop -> Clausula
-- tal que (clausula f) es la cláusula de la fórmula clausal f. Por
-- ejemplo,
--    clausula p                                 ==  [p]
--    clausula (no p)                            ==  [no p]
--    clausula (((no p) \/ r) \/ ((no p) \/ q))  ==  [q,r,no p]
-- ---------------------------------------------------------------------

clausula :: Prop -> Clausula
clausula f | literal f = [f]
clausula (Disj f g)    = sort (clausula f `union` clausula g)
clausula _             = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    clausulasFNC :: Prop -> [Clausula]
-- tal que (clausulasFNC f) es el conjunto de cláusulas de la fórmula en
-- forma normal conjuntiva f. Por ejmplo,
--    clausulasFNC (p /\ ((no q) \/ r))
--    == [[p],[r, no q]]
--    clausulasFNC (((no p) \/ q) /\ ((no p) \/ (no r)))
--    == [[q, no p],[no p,no r]]
-- ---------------------------------------------------------------------

clausulasFNC :: Prop -> [Clausula]
clausulasFNC (Conj f g) = clausulasFNC f `union` clausulasFNC g
clausulasFNC f          = [clausula f]

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
--    clausulas :: Prop -> [Clausula]
-- tal que (clausulas f) es un conjunto de cláusulas equivalente a
-- f. Por ejemplo,
--    clausulas (p /\ (q --> r))
--    == [[p],[r,no q]]
--    clausulas (no (p /\ (q --> r)))
--    == [[q,no p],[no p,no r]]
--    clausulas (no(p <--> r))
--    == [[p,r],[p,no p],[r,no r],[no p,no r]]
-- ---------------------------------------------------------------------

-- 1ª definición
clausulas1 :: Prop -> [Clausula]
clausulas1 f = clausulasFNC (formaNormalConjuntiva f)

-- 2ª definición
clausulas :: Prop -> [Clausula]
clausulas = clausulasFNC . formaNormalConjuntiva

-- ---------------------------------------------------------------------
-- § Cláusulas de un conjunto de fórmulas                             --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    clausulasConjunto :: [Prop] -> [Clausula]
-- tal que (clausulasConjunto cs) es un conjunto de cláusulas equivalente
-- a cs. Por ejemplo,
--    clausulasConjunto [p --> q, q --> r]   ==  [[q,no p],[r,no q]]
--    clausulasConjunto [p --> q, q <--> p]  ==  [[q,no p],[p,no q]]
-- ---------------------------------------------------------------------

-- 1ª definición
clausulasConjunto1 :: [Prop] -> [Clausula]
clausulasConjunto1 cs = unionGeneral [clausulas f | f <- cs]

-- 2ª definición
clausulasConjunto2 :: [Prop] -> [Clausula]
clausulasConjunto2 cs = unionGeneral (map clausulas cs)

-- 3ª definición
clausulasConjunto :: [Prop] -> [Clausula]
clausulasConjunto = unionGeneral . map clausulas

-- ---------------------------------------------------------------------
-- § Símbolos proposicionales de una cláusula                         --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir la función
--    simbolosProposicionalesClausula :: Clausula -> [Prop]
-- tal que (simbolosProposicionalesClausula c) es el conjunto de los
-- símbolos proposicionales de c. Por ejemplo,
--    simbolosProposicionalesClausula [p, q, no p]  ==  [p,q]
-- ---------------------------------------------------------------------

-- 1ª definición
simbolosProposicionalesClausula1 :: Clausula -> [Prop]
simbolosProposicionalesClausula1 c = simbolosPropConj c

-- 2ª definición
simbolosProposicionalesClausula :: Clausula -> [Prop]
simbolosProposicionalesClausula = simbolosPropConj

-- ---------------------------------------------------------------------
-- § Símbolos proposicionales de un conjunto de clausulas             --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir la función
--    simbolosProposicionalesConjuntoClausula :: [Clausula] -> [Prop]
-- tal que (simbolosProposicionalesConjuntoClausula cs) es el conjunto
-- de los símbolos proposicionales de cs. Por ejemplo,
--    simbolosProposicionalesConjuntoClausula [[p, q],[no q, r]]
--    == [p,q,r]
-- ---------------------------------------------------------------------

-- 1ª definición
simbolosProposicionalesConjuntoClausula1 :: [Clausula] -> [Prop]
simbolosProposicionalesConjuntoClausula1 cs =
  unionGeneral [simbolosProposicionalesClausula c | c <- cs]

-- 2ª definición
simbolosProposicionalesConjuntoClausula2 :: [Clausula] -> [Prop]
simbolosProposicionalesConjuntoClausula2 cs =
  unionGeneral (map simbolosProposicionalesClausula cs)

-- 3ª definición
simbolosProposicionalesConjuntoClausula :: [Clausula] -> [Prop]
simbolosProposicionalesConjuntoClausula =
  unionGeneral . map simbolosProposicionalesClausula

-- ---------------------------------------------------------------------
-- § Interpretaciones de una cláusula                                 --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    interpretacionesClausula :: Clausula -> [Interpretacion]
-- tal que (interpretacionesClausula c) es el conjunto de
-- interpretaciones de c. Por ejemplo,
--    interpretacionesClausula [p, q, no p]  ==  [[p,q],[p],[q],[]]
--    interpretacionesClausula []            ==  [[]]
-- ---------------------------------------------------------------------

-- 1ª definición
interpretacionesClausula1 :: Clausula -> [Interpretacion]
interpretacionesClausula1 c =
  subconjuntos (simbolosProposicionalesClausula c)

-- 2ª definición
interpretacionesClausula :: Clausula -> [Interpretacion]
interpretacionesClausula =
  subconjuntos . simbolosProposicionalesClausula

-- ---------------------------------------------------------------------
-- § Interpretaciones de un conjunto de cláusulas                     --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    interpretacionesConjuntoClausula :: [Clausula] -> [Interpretacion]
-- tal que (interpretacionesConjuntoClausula cs) es el conjunto de
-- interpretaciones de cs. Por ejemplo,
--    interpretacionesConjuntoClausula [[p, no q],[no p, q]]
--    == [[p,q],[p],[q],[]]
--    interpretacionesConjuntoClausula []
--    == [[]]
-- ---------------------------------------------------------------------

-- 1ª definición
interpretacionesConjuntoClausula1 :: [Clausula] -> [Interpretacion]
interpretacionesConjuntoClausula1 cs =
  subconjuntos (simbolosProposicionalesConjuntoClausula cs)

-- 2ª definición
interpretacionesConjuntoClausula :: [Clausula] -> [Interpretacion]
interpretacionesConjuntoClausula =
  subconjuntos . simbolosProposicionalesConjuntoClausula

-- ---------------------------------------------------------------------
-- § Modelos de cláusulas                                             --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    esModeloLiteral :: Interpretacion -> Literal -> Bool
-- tal que (esModeloLiteral i l) se verifica si i es modelo de l. Por
-- ejemplo,
--    esModeloLiteral [p,r] p       ==  True
--    esModeloLiteral [p,r] q       ==  False
--    esModeloLiteral [p,r] (no p)  ==  False
--    esModeloLiteral [p,r] (no q)  ==  True
-- ---------------------------------------------------------------------

esModeloLiteral :: Interpretacion -> Literal -> Bool
esModeloLiteral i (Atom a)       = Atom a `elem` i
esModeloLiteral i (Neg (Atom a)) = Atom a `notElem` i
esModeloLiteral _ _              = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    esModeloClausula :: Interpretacion -> Clausula -> Bool
-- tal que (esModeloClausula i c) se verifica si i es modelo de c . Por
-- ejemplo,
--    esModeloClausula [p,r] [p, q]     ==  True
--    esModeloClausula [r] [p, no q]    ==  True
--    esModeloClausula [q,r] [p, no q]  ==  False
--    esModeloClausula [q,r] []         ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esModeloClausula1 :: Interpretacion -> Clausula -> Bool
esModeloClausula1 i c =
  or [esModeloLiteral i l | l <- c]

-- 2ª definición
esModeloClausula2 :: Interpretacion -> Clausula -> Bool
esModeloClausula2 i c =
  any (esModeloLiteral i) c

-- 3ª definición
esModeloClausula :: Interpretacion -> Clausula -> Bool
esModeloClausula =
  any . esModeloLiteral

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    modelosClausula :: Clausula -> [Interpretacion]
-- tal que (modelosClausula c) es la lista de los modelos de c. Por
-- ejemplo,
--    modelosClausula [no p, q]  ==  [[p,q],[q],[]]
--    modelosClausula [no p, p]  ==  [[p],[]]
--    modelosClausula []         ==  []
-- ---------------------------------------------------------------------

-- 1ª definición
modelosClausula1 :: Clausula -> [Interpretacion]
modelosClausula1 c =
  [i | i <- interpretacionesClausula c,
       esModeloClausula i c]

-- 2ª definición
modelosClausula2 :: Clausula -> [Interpretacion]
modelosClausula2 c =
  filter (`esModeloClausula` c) (interpretacionesClausula c)

-- 3ª definición
modelosClausula :: Clausula -> [Interpretacion]
modelosClausula =
  (filter . flip esModeloClausula) <*> interpretacionesClausula

-- ---------------------------------------------------------------------
-- § Modelos de conjuntos de cláusulas                                --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    esModeloConjuntoClausulas :: Interpretacion -> [Clausula] -> Bool
-- tal que (esModeloConjuntoClausulas i cs) se verifica si i es modelo
-- de cs. Por ejemplo,
--    esModeloConjuntoClausulas [p,r] [[p, no q], [r]]  ==  True
--    esModeloConjuntoClausulas [p] [[p, no q], [r]]    ==  False
--    esModeloConjuntoClausulas [p] []                  ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esModeloConjuntoClausulas1 :: Interpretacion -> [Clausula] -> Bool
esModeloConjuntoClausulas1 i cs =
  and [esModeloClausula i c | c <- cs]

-- 2ª definición
esModeloConjuntoClausulas2 :: Interpretacion -> [Clausula] -> Bool
esModeloConjuntoClausulas2 i cs =
  all (esModeloClausula i) cs

-- 3ª definición
esModeloConjuntoClausulas :: Interpretacion -> [Clausula] -> Bool
esModeloConjuntoClausulas =
  all . esModeloClausula

-- ---------------------------------------------------------------------
-- Ejercicio 14: Definir la función
--    modelosConjuntoClausulas :: [Clausula] -> [Interpretacion]
-- tal que (modelosConjuntoClausulas cs) es la lista de los modelos de
-- cs. Por ejemplo,
--    modelosConjuntoClausulas [[no p, q], [no q, p]]
--    == [[p,q],[]]
--    modelosConjuntoClausulas [[no p, q], [p], [no q]]
--    == []
--    modelosConjuntoClausulas [[p, no p, q]]
--    == [[p,q],[p],[q],[]]
-- ---------------------------------------------------------------------

-- 1ª definición
modelosConjuntoClausulas1 :: [Clausula] -> [Interpretacion]
modelosConjuntoClausulas1 cs =
  [i | i <- interpretacionesConjuntoClausula cs,
       esModeloConjuntoClausulas i cs]

-- 2ª definición
modelosConjuntoClausulas2 :: [Clausula] -> [Interpretacion]
modelosConjuntoClausulas2 cs =
  filter (`esModeloConjuntoClausulas` cs)  (interpretacionesConjuntoClausula cs)

-- 3ª definición
modelosConjuntoClausulas :: [Clausula] -> [Interpretacion]
modelosConjuntoClausulas =
  (filter . flip esModeloConjuntoClausulas) <*> interpretacionesConjuntoClausula

-- ---------------------------------------------------------------------
-- § Cláusulas válidas, satisfacibles e insatisfacibles               --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 15: Definir la función
--    esClausulaValida :: Clausula -> Bool
-- tal que (esClausulaValida c) se verifica si la clausula c es
-- válida. Por ejemplo,
--    esClausulaValida [p, q, no p]  ==  True
--    esClausulaValida [p, q, no r]  ==  False
--    esClausulaValida []            ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esClausulaValida1 :: Clausula -> Bool
esClausulaValida1 c =
  [l | l <- c, complementario l `elem` c] /= []

-- 2ª definición
esClausulaValida2 :: Clausula -> Bool
esClausulaValida2 c =
  not (null (filter (\l -> complementario l `elem` c) c))

-- 3ª definición
esClausulaValida3 :: Clausula -> Bool
esClausulaValida3 =
  not . null . (filter =<< flip (elem . complementario))

-- 4ª definición
esClausulaValida4 :: Clausula -> Bool
esClausulaValida4 c =
  and [esModeloClausula i c | i <- interpretacionesClausula c]

-- 5ª definición
esClausulaValida5 :: Clausula -> Bool
esClausulaValida5 c =
  all (`esModeloClausula` c) (interpretacionesClausula c)

-- 6ª definición
esClausulaValida :: Clausula -> Bool
esClausulaValida =
  (all . flip esModeloClausula) <*> interpretacionesClausula

-- ---------------------------------------------------------------------
-- Ejercicio 16: Definir la función
--    esClausulaInsatisfacible :: Clausula -> Bool
-- tal que (esClausulaInsatisfacible c) se verifica si la cláusula c es
-- insatisfacible. Por ejemplo,
--    esClausulaInsatisfacible [p, q, no p]  ==  False
--    esClausulaInsatisfacible [p, q, no r]  ==  False
--    esClausulaInsatisfacible []            ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esClausulaInsatisfacible1 :: Clausula -> Bool
esClausulaInsatisfacible1 c = null c

-- 2ª definición
esClausulaInsatisfacible :: Clausula -> Bool
esClausulaInsatisfacible = null

-- 3ª definición
esClausulaInsatisfacible3 :: Clausula -> Bool
esClausulaInsatisfacible3 c =
  and [not (esModeloClausula i c) | i <- interpretacionesClausula c]

-- 4ª definición
esClausulaInsatisfacible4 :: Clausula -> Bool
esClausulaInsatisfacible4 c =
  all (not . (`esModeloClausula` c)) (interpretacionesClausula c)

-- 4ª definición
esClausulaInsatisfacible5 :: Clausula -> Bool
esClausulaInsatisfacible5 =
  (all . (not .) . flip esModeloClausula) <*> interpretacionesClausula

-- ---------------------------------------------------------------------
-- Ejercicio 17: Definir la función
--    esClausulaSatisfacible :: Clausula -> Bool
-- tal que (esClausulaSatisfacible c) se verifica si la cláusula c es
-- satisfacible. Por ejemplo,
--    esClausulaSatisfacible [p, q, no p]  ==  True
--    esClausulaSatisfacible [p, q, no r]  ==  True
--    esClausulaSatisfacible []  ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esClausulaSatisfacible1 :: Clausula -> Bool
esClausulaSatisfacible1 c = not (null c)

-- 2ª definición
esClausulaSatisfacible :: Clausula -> Bool
esClausulaSatisfacible = not . null

-- 3ª definición
esClausulaSatisfacible3 :: Clausula -> Bool
esClausulaSatisfacible3 c =
  or [esModeloClausula i c | i <- interpretacionesClausula c]

-- 4ª definición
esClausulaSatisfacible4 :: Clausula -> Bool
esClausulaSatisfacible4 c =
  any (`esModeloClausula` c) (interpretacionesClausula c)

-- 5ª definición
esClausulaSatisfacible5 :: Clausula -> Bool
esClausulaSatisfacible5 =
  (any . flip esModeloClausula) <*> interpretacionesClausula

-- ---------------------------------------------------------------------
-- § Conjuntos válidos, consistentes e inconsistentes de cláusulas    --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 18: Definir la función
--    esConjuntoValidoDeClausulas :: [Clausula] -> Bool
-- tal que (esConjuntoValidoDeClausulas cs) se verifica si el conjunto de
-- clausulas cs es válido. Por ejemplo,
--    esConjuntoValidoDeClausulas [[no p, q], [no q, p]]  ==  False
--    esConjuntoValidoDeClausulas [[no p, p], [no q, q]]  ==  True
--    esConjuntoValidoDeClausulas []                      ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esConjuntoValidoDeClausulas1 :: [Clausula] -> Bool
esConjuntoValidoDeClausulas1 cs = and [esClausulaValida c | c <- cs]

-- 2ª definición
esConjuntoValidoDeClausulas2 :: [Clausula] -> Bool
esConjuntoValidoDeClausulas2 cs = all esClausulaValida cs

-- 3ª definición
esConjuntoValidoDeClausulas :: [Clausula] -> Bool
esConjuntoValidoDeClausulas = all esClausulaValida

-- 4ª definición
esConjuntoValidoDeClausulas4 :: [Clausula] -> Bool
esConjuntoValidoDeClausulas4 cs =
  modelosConjuntoClausulas cs == interpretacionesConjuntoClausula cs

-- 5ª definición
esConjuntoValidoDeClausulas5 :: [Clausula] -> Bool
esConjuntoValidoDeClausulas5 =
  (==) <$> modelosConjuntoClausulas <*> interpretacionesConjuntoClausula

-- ---------------------------------------------------------------------
-- Ejercicio 19: Definir la función
--    esConjuntoConsistenteDeClausulas :: [Clausula] -> Bool
-- tal que (esConjuntoConsistenteDeClausulas cs) se verifica si el
-- conjunto de cláusulas cs es consistente. Por ejemplo,
--    esConjuntoConsistenteDeClausulas [[no p, q], [no q, p]]  ==  True
--    esConjuntoConsistenteDeClausulas [[no p, p], [no q, q]]  ==  True
--    esConjuntoConsistenteDeClausulas []                      ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esConjuntoConsistenteDeClausulas1 :: [Clausula] -> Bool
esConjuntoConsistenteDeClausulas1 cs =
  not (null (modelosConjuntoClausulas cs))

-- 2ª definición
esConjuntoConsistenteDeClausulas :: [Clausula] -> Bool
esConjuntoConsistenteDeClausulas =
  not . null . modelosConjuntoClausulas

-- ---------------------------------------------------------------------
-- Ejercicio 20: Definir la función
--    esConjuntoInconsistenteDeClausulas :: [Clausula] -> Bool
-- tal que (esConjuntoInconsistenteDeClausulas cs) se verifica si el
-- conjunto de clausulas cs es consistente. Por ejemplo,
--    esConjuntoInconsistenteDeClausulas [[no p,q],[no q,p]]  ==  False
--    esConjuntoInconsistenteDeClausulas [[no p],[p]]         ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esConjuntoInconsistenteDeClausulas1 :: [Clausula] -> Bool
esConjuntoInconsistenteDeClausulas1 cs =
  null (modelosConjuntoClausulas cs)

-- 2ª definición
esConjuntoInconsistenteDeClausulas :: [Clausula] -> Bool
esConjuntoInconsistenteDeClausulas =
  null . modelosConjuntoClausulas

-- ---------------------------------------------------------------------
-- § Validez de fórmulas mediante cláusulas                           --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 21: Definir la función
--    esValidaPorClausulas :: Prop -> Bool
-- tal que (esValidaPorClausulas f) se verifica si el conjunto de
-- cláusulas de f es válido. Por ejemplo,
--    esValidaPorClausulas (p --> q)                 ==  False
--    esValidaPorClausulas (p --> p)                 ==  True
--    esValidaPorClausulas ((p --> q) \/ (q --> p))  ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
esValidaPorClausulas1 :: Prop -> Bool
esValidaPorClausulas1 f =
  esConjuntoValidoDeClausulas (clausulas f)

-- 2ª definición
esValidaPorClausulas :: Prop -> Bool
esValidaPorClausulas =
  esConjuntoValidoDeClausulas . clausulas

-- ---------------------------------------------------------------------
-- § Consecuencia mediante cláusulas                                  --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 22: Definir la función
--    esConsecuenciaEntreClausulas :: [Clausula] -> [Clausula] -> Bool
-- tal que (esConsecuenciaEntreClausulas s1 s2) se verifica si todos los
-- modelos de s1 son modelos de s2. Por ejemplo,
--    esConsecuenciaEntreClausulas [[no p,q],[no q,r]] [[no p,r]]
--    == True
--    esConsecuenciaEntreClausulas [[p]] [[p],[q]]
--    == False
-- ---------------------------------------------------------------------

esConsecuenciaEntreClausulas :: [Clausula] -> [Clausula] -> Bool
esConsecuenciaEntreClausulas s1 s2 =
  null [i | i <- interpretacionesConjuntoClausula (s1++s2)
          , esModeloConjuntoClausulas i s1
          , not ((esModeloConjuntoClausulas i s2))]

-- ---------------------------------------------------------------------
-- Ejercicio 23: Definir la función
--    esConsecuenciaPorClausulas :: [Prop] -> Prop -> Bool
-- tal que (esConsecuenciaPorClausulas cs f) se verifica si las cláusulas
-- de f son consecuencias de las de cs. Por ejemplo,
--    esConsecuenciaPorClausulas [(p --> q), (q --> r)] (p --> r)
--    == True
--    esConsecuenciaPorClausulas [p] (p /\ q)
--    == False
-- ---------------------------------------------------------------------

-- 1ª definición
esConsecuenciaPorClausulas :: [Prop] -> Prop -> Bool
esConsecuenciaPorClausulas cs f =
  esConsecuenciaEntreClausulas (clausulasConjunto cs) (clausulas f)

-- 2ª definición
esConsecuenciaPorClausulas2 :: [Prop] -> Prop -> Bool
esConsecuenciaPorClausulas2 cs f =
  esConjuntoInconsistenteDeClausulas (clausulasConjunto (Neg f : cs))

-- 3ª definición
esConsecuenciaPorClausulas3 :: [Prop] -> Prop -> Bool
esConsecuenciaPorClausulas3 =
  (. clausulas) . esConsecuenciaEntreClausulas . clausulasConjunto
