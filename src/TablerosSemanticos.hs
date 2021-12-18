-- TablerosSemánticos.hs
-- Tableros semánticos proposicionales.
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module TablerosSemanticos where

-- ---------------------------------------------------------------------
-- § Introducción                                                     --
-- ---------------------------------------------------------------------

-- En este módulo se implementa el método de los tableros semánticos
-- proposicionales siguiendo su exposición en el tema 3 de la asignatura
-- de "Lógica informática" que se encuentra en https://bit.ly/3mgrK4q

-- ---------------------------------------------------------------------
-- § Librerías auxiliares                                             --
-- ---------------------------------------------------------------------

import SintaxisSemantica (
  Prop (..),
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
  unionGeneral
  )
import FormasNormales (
  literal
  )
import Data.List (
  delete,
  union
  )

-- ---------------------------------------------------------------------
-- § Notación uniforme                                                --
-- ---------------------------------------------------------------------

-- Nota: En los ejemplos se usará la notación de fórmulas del módulo
-- SintaxisSemantica. Por ejemplo,
ejFormula :: Prop
ejFormula = p --> q /\ (r <--> no p1 \/ (p2 /\ s))

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir la función
--    dobleNegacion :: Prop -> Bool
-- tal que (dobleNegacion f) se verifica si f es una doble negación. Por
-- ejemplo,
--    dobleNegacion (no (no p))     ==  True
--    dobleNegacion (no (p --> q))  ==  False
-- ---------------------------------------------------------------------

dobleNegacion :: Prop -> Bool
dobleNegacion (Neg (Neg _)) = True
dobleNegacion _             = False

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir la función
--    alfa :: Prop -> Bool
-- tal que (alfa f) se verifica si f es una fórmula alfa.
-- ---------------------------------------------------------------------

alfa :: Prop -> Bool
alfa (Conj _ _)       = True
alfa (Neg (Impl _ _)) = True
alfa (Neg (Disj _ _)) = True
alfa _                = False

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    beta :: Prop -> Bool
-- tal que (beta d) se verifica si f es una fórmula beta.
-- ---------------------------------------------------------------------

beta :: Prop -> Bool
beta (Disj _ _)       = True
beta (Impl _ _)       = True
beta (Neg (Conj _ _)) = True
beta (Equi _ _)       = True
beta (Neg (Equi _ _)) = True
beta _                = False

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
--    componentes :: Prop -> [Prop]
-- tal que (componentes ) es la lista de las componentes de la fórmula
-- f. Por ejemplo,
--    componentes (p /\ q --> r)       ==  [no (p /\ q),r]
--    componentes (no (p /\ q --> r))  ==  [(p /\ q),no r]
-- ---------------------------------------------------------------------

componentes :: Prop -> [Prop]
componentes (Neg (Neg f))    = [f]
componentes (Conj f g)       = [f, g]
componentes (Neg (Impl f g)) = [f, Neg g]
componentes (Neg (Disj f g)) = [Neg f, Neg g]
componentes (Disj f g)       = [f, g]
componentes (Impl f g)       = [Neg f, g]
componentes (Neg (Conj f g)) = [Neg f, Neg g]
componentes (Equi f g)       = [Conj f g, Conj (Neg f) (Neg g)]
componentes (Neg (Equi f g)) = [Conj f (Neg g), Conj (Neg f) g]
componentes _                = error "Imposible"

-- ---------------------------------------------------------------------
-- § Modelos mediante tableros                                        --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    conjuntoDeLiterales :: [Prop] -> Bool
-- tal que (conjuntoDeLiterales fs) se verifica si fs es un conjunto de
-- literales. Por ejemplo,
--    conjuntoDeLiterales [p --> q, no r, r /\ s, p]  ==  False
--    conjuntoDeLiterales [p, no q, r]                ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
conjuntoDeLiterales1 :: [Prop] -> Bool
conjuntoDeLiterales1 fs =
  and [literal f | f <- fs]

-- 2ª definición
conjuntoDeLiterales2 :: [Prop] -> Bool
conjuntoDeLiterales2 fs =
  all literal fs

-- 3ª definición
conjuntoDeLiterales :: [Prop] -> Bool
conjuntoDeLiterales =
  all literal

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir la función
--    tieneContradiccion :: [Prop] -> Bool
-- tal que (tieneContradiccion fs) se verifica si fs contiene una
-- fórmula y su negación. Por ejemplo,
--    tieneContradiccion [r, p /\ q, s, no(p /\ q)]  ==  True
-- ---------------------------------------------------------------------

-- 1ª definición
tieneContradiccion1 :: [Prop] -> Bool
tieneContradiccion1 fs =
  [f | f <- fs, Neg f `elem` fs] /= []

-- 2ª definición
tieneContradiccion :: [Prop] -> Bool
tieneContradiccion fs =
  not (null [f | f <- fs, Neg f `elem` fs])

-- 3ª definición
tieneContradiccion3 :: [Prop] -> Bool
tieneContradiccion3 fs =
  not (null (filter (\f -> Neg f `elem` fs) fs))

-- 4ª definición
tieneContradiccion4 :: [Prop] -> Bool
tieneContradiccion4 fs =
  any (\ f -> Neg f `elem` fs) fs

-- 5ª definición
tieneContradiccion5 :: [Prop] -> Bool
tieneContradiccion5 =
  any =<< flip (elem . Neg)

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir la función
--    expansionDN :: [Prop] -> Prop -> [[Prop]]
-- tal que (expansionDN fs f) es la expansión de fs mediante la doble
-- negación f. Por ejemplo,
--    expansionDN [p, no(no q), r] (no(no q))  ==  [[q,p,r]]
-- ---------------------------------------------------------------------

expansionDN :: [Prop] -> Prop -> [[Prop]]
expansionDN fs f =
  [componentes f `union` delete f fs]

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    expansionAlfa :: [Prop] -> Prop -> [[Prop]]
-- tal que (expansionAlfa fs f) es la expansión de fs mediante la
-- fórmula alfa f. Por ejemplo,
--    expansionAlfa [q, (p1 /\ p2) , r] (p1 /\ p2)  ==  [[p1,p2,q,r]]
-- ---------------------------------------------------------------------

expansionAlfa :: [Prop] -> Prop -> [[Prop]]
expansionAlfa fs f =
  [componentes f `union` delete f fs]

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    expansionBeta :: [Prop] -> Prop -> [[Prop]]
-- tal que (expansionBeta fs f) es la expansión de fs mediante la
-- fórmula beta f. Por ejemplo,
--    expansionBeta [q, (p1 \/ p2) , r] (p1 \/ p2)  ==  [[p1,q,r],[p2,q,r]]
-- ---------------------------------------------------------------------

expansionBeta :: [Prop] -> Prop -> [[Prop]]
expansionBeta fs f =
  [[g] `union` delete f fs | g <- componentes f]

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    sucesores :: [Prop] -> [[Prop]]
-- tal que (sucesores fs) es la lista de sucesores de fs. Por ejemplo,
--    sucesores [q \/ s, no(no r), p1 /\ p2] == [[r,(q \/ s),(p1 /\ p2)]]
--    sucesores [r,(q \/ s),(p1 /\ p2)]      == [[p1,p2,r,(q \/ s)]]
--    sucesores [p1,p2,r,(q \/ s)]           == [[q,p1,p2,r],[s,p1,p2,r]]
-- ---------------------------------------------------------------------

-- 1ª definición
sucesores1 :: [Prop] -> [[Prop]]
sucesores1 fs
  | doblesNegacion /= []  = expansionDN   fs (head doblesNegacion)
  | alfas /= []           = expansionAlfa fs (head alfas)
  | betas /= []           = expansionBeta fs (head betas)
  | otherwise             = error "Imposible"
  where doblesNegacion = [f | f <- fs, dobleNegacion f]
        alfas          = [f | f <- fs, alfa f]
        betas          = [f | f <- fs, beta f]

-- 2ª definición
sucesores :: [Prop] -> [[Prop]]
sucesores fs
  | not (null doblesNegacion) = expansionDN   fs (head doblesNegacion)
  | not (null alfas)          = expansionAlfa fs (head alfas)
  | not (null betas)          = expansionBeta fs (head betas)
  | otherwise             = error "Imposible"
  where doblesNegacion = filter dobleNegacion fs
        alfas          = filter alfa fs
        betas          = filter beta fs

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    modelosTab :: [Prop] -> [[Prop]]
-- tal que (modelosTab fs) es el conjunto de los modelos de fs
-- calculados mediante el método de tableros semánticos. Por ejemplo,
--    modelosTab [p --> q, no(q --> p)]
--    == [[no p,q],[q,no p]]
--    modelosTab [p --> q, no q --> no p]
--    == [[q,no p],[no p],[q],[no p,q]]
-- ---------------------------------------------------------------------

modelosTab :: [Prop] -> [[Prop]]
modelosTab fs
  | tieneContradiccion fs  = []
  | conjuntoDeLiterales fs = [fs]
  | otherwise              = unionGeneral [modelosTab gs
                                           | gs <- sucesores fs]

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    subconjunto :: Eq a => [a] -> [a] -> Bool
-- tal que (subconjunto x y) se verifica si x es subconjunto de y. Por
-- ejemplo,
--    subconjunto [1,3] [3,2,1]    ==  True
--    subconjunto [1,3,5] [3,2,1]  == False
-- ---------------------------------------------------------------------

-- 1ª definición
subconjunto :: Eq a => [a] -> [a] -> Bool
subconjunto xs ys =
  and [x `elem` ys | x <- xs]

-- 2ª definición
subconjunto2 :: Eq a => [a] -> [a] -> Bool
subconjunto2 xs ys =
  all (`elem` ys) xs

-- 3ª definición
subconjunto3 :: Eq a => [a] -> [a] -> Bool
subconjunto3 =
  flip (all . flip elem)

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    modelosGenerales :: [Prop] -> [[Prop]]
-- tal que (modelosGenerales fs) es el conjunto de los modelos generales
-- de fs calculados mediante el método de tableros semánticos. Por
-- ejemplo,
--    modelosGenerales [p --> q, no q --> no p]  ==  [[no p],[q]]
-- ---------------------------------------------------------------------

modelosGenerales :: [Prop] -> [[Prop]]
modelosGenerales fs =
  [gs | gs <- modelos
      , null [hs | hs <- delete gs modelos, subconjunto hs gs]]
  where modelos = modelosTab fs

-- ---------------------------------------------------------------------
-- § Teoremas por tableros                                            --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 14: Definir la función
--    esTeoremaPorTableros :: Prop -> Bool
-- tal que (esTeoremaPorTableros f) se verifica si la fórmula f es
-- teorema (mediante tableros semánticos). Por ejemplo,
--    esTeoremaPorTableros (p --> p)  ==  True
--    esTeoremaPorTableros (p --> q)  ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esTeoremaPorTableros :: Prop -> Bool
esTeoremaPorTableros f =
  null (modelosTab [Neg f])

-- 2ª definición
esTeoremaPorTableros2 :: Prop -> Bool
esTeoremaPorTableros2 =
  null . modelosTab . return . Neg

-- ---------------------------------------------------------------------
-- § Consecuencia por tableros                                        --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 15: Definir la función
--    esDeduciblePorTableros :: [Prop] -> Prop -> Bool
-- tal que (esDeduciblePorTableros fs f) se verifica si la fórmula f es
-- consecuencia (mediante tableros) del conjunto de fórmulas fs. Por
-- ejemplo,
--    esDeduciblePorTableros [p --> q, q --> r] (p --> r)   ==  True
--    esDeduciblePorTableros [p --> q, q --> r] (p <--> r)  ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esDeduciblePorTableros :: [Prop] -> Prop -> Bool
esDeduciblePorTableros fs f =
  null (modelosTab (Neg f : fs))

-- 2ª definición
esDeduciblePorTableros2 :: [Prop] -> Prop -> Bool
esDeduciblePorTableros2 =
  ((null . modelosTab) .) . flip ((:) . Neg)
