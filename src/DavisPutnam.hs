-- DavisPutnam.hs
-- El procedimiento de Davis y Putnam
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module DavisPutnam where

-- ---------------------------------------------------------------------
-- § Introducción                                                     --
-- ---------------------------------------------------------------------

-- En este módulo se implementa el procedimiento de Davis-Putnam
-- siguiendo su exposición en el tema 6 de la asignatura de "Lógica
-- informática" que se encuentra en https://bit.ly/3pG72gt

-- ---------------------------------------------------------------------
-- § Librerías auxiliares                                             --
-- ---------------------------------------------------------------------

import SintaxisSemantica
import FormasNormales
import Clausulas
import Data.List

-- ---------------------------------------------------------------------
-- § Eliminación de tautologías                                       --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir la función
--    esTautologia :: Clausula -> Bool
-- tal que (esTautologia c) se verifica si c es una tautología. Por
-- ejemplo,
--    esTautologia [p, q, no p]  ==  True
--    esTautologia [p, q, no r]  ==  False
--    esTautologia []            ==  False
-- ---------------------------------------------------------------------

-- 1ª definición
esTautologia :: Clausula -> Bool
esTautologia c =
  [f | f <- c, complementario f `elem` c] /= []

-- 2ª definición
esTautologia2 :: Clausula -> Bool
esTautologia2 c =
  not (null [f | f <- c, complementario f `elem` c])

-- 3ª definición
esTautologia3 :: Clausula -> Bool
esTautologia3 c =
  not (null (filter (\f -> complementario f `elem` c) c))

-- 4ª definición
esTautologia4 :: Clausula -> Bool
esTautologia4 c =
  any (\ f -> complementario f `elem` c) c

-- 5ª definición
esTautologia5 :: Clausula -> Bool
esTautologia5  =
  any =<< flip (elem . complementario)

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir la función
--    eliminaTautologias :: [Clausula] -> [Clausula]
-- tal que (eliminaTautologias cs) es el conjunto obtenido eliminando las
-- tautologías de cs. Por ejemplo,
--    eliminaTautologias [[p, q], [p, q, no p]]  ==  [[p,q]]
-- ---------------------------------------------------------------------

-- 1ª definición
eliminaTautologias :: [Clausula] -> [Clausula]
eliminaTautologias cs =
  [c | c <- cs, not (esTautologia c)]

-- 2ª definición
eliminaTautologias2 :: [Clausula] -> [Clausula]
eliminaTautologias2 =
  filter (not . esTautologia)

-- ---------------------------------------------------------------------
-- § Eliminación de cláusulas unitarias                               --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    esUnitaria :: Clausula -> Bool
-- tal que (esUnitaria c) se verifica si la cláusula c es unitaria . Por
-- ejemplo,
--    esUnitaria [p]     ==  True
--    esUnitaria [no p]  ==  True
--    esUnitaria [p, q]  ==  False
-- ---------------------------------------------------------------------

esUnitaria :: Clausula -> Bool
esUnitaria [_] = True
esUnitaria _   = False

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
--    eliminaClausulaUnitaria :: Literal -> [Clausula] -> [Clausula]
-- tal que (eliminaClausulaUnitaria l cs) es el conjunto obtenido al
-- reducir cs por la eliminación de la cláusula unitaria formada por el
-- literal l. Por ejemplo,
--    eliminaClausulaUnitaria (no p) [[p,q,no r],[p,no q],[no p],[r]]
--    == [[q,no r],[no q],[r]]
--    eliminaClausulaUnitaria (no q) [[q,no r],[no q],[r]]
--    == [[no r],[r]]
--    eliminaClausulaUnitaria (no r) [[no r],[r],[p]]
--    == [[],[p]]
-- ---------------------------------------------------------------------

eliminaClausulaUnitaria :: Literal -> [Clausula] -> [Clausula]
eliminaClausulaUnitaria l cs =
  [delete (complementario l) c | c <- cs, l `notElem` c]

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    clausulaUnitaria :: [Clausula] -> Maybe Literal
-- tal que (clausulaUnitaria s) es la primera cláusula unitaria de cs, si
-- cs tiene cláusulas unitarias y nada en caso contrario. Por ejemplo,
--    clausulaUnitaria [[p,q],[p],[no q]]  ==  Just p
--    clausulaUnitaria [[p,q],[p,no q]]    ==  Nothing
-- ---------------------------------------------------------------------

clausulaUnitaria :: [Clausula] -> Maybe Literal
clausulaUnitaria [] = Nothing
clausulaUnitaria (c:cs)
  | esUnitaria c = Just (head c)
  | otherwise    = clausulaUnitaria cs

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir la función
--    eliminaClausulasUnitarias :: [Clausula] -> [Clausula]
-- tal que (eliminaClausulasUnitarias cs) es el conjunto obtenido
-- aplicando el proceso de eliminación de cláusulas unitarias a cs. Por
-- ejemplo,
--    eliminaClausulasUnitarias [[p,q,no r],[p,no q],[no p],[r],[u]]
--    == [[],[u]]
--    eliminaClausulasUnitarias [[p,q],[no q],[no p,q,no r]]
--    == []
--    eliminaClausulasUnitarias [[no p,q],[p],[r,u]]
--    == [[r,u]]
-- ---------------------------------------------------------------------

eliminaClausulasUnitarias :: [Clausula] -> [Clausula]
eliminaClausulasUnitarias cs
  | [] `elem ` cs                  = cs
  | clausulaUnitaria cs == Nothing = cs
  | otherwise                      =
      eliminaClausulasUnitarias (eliminaClausulaUnitaria c cs)
      where Just c = clausulaUnitaria cs

-- ---------------------------------------------------------------------
-- § Eliminación de literales puros                                   --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir la función
--    literales :: [Clausula] -> [Literal]
-- tal que (literales cs) es el conjunto de literales de ss. Por ejemplo,
--    literales [[p,q],[p,q,no p]]  ==  [p,q,no p]
-- ---------------------------------------------------------------------

literales :: [Clausula] -> [Literal]
literales =
  unionGeneral

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    esLiteralPuro :: Literal -> [Clausula] -> Bool
-- tal que (esLiteralPuro l cs) se verifica si l es puro en cs. Por
-- ejemplo,
--    esLiteralPuro p [[p,q],[p,no q],[r,q],[r,no q]]  ==  True
--    esLiteralPuro q [[p,q],[p,no q],[r,q],[r,no q]]  ==  False
-- ---------------------------------------------------------------------

esLiteralPuro :: Literal -> [Clausula] -> Bool
esLiteralPuro l cs =
  and [l' `notElem` c | c <- cs]
  where l' = complementario l

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    eliminaLiteralPuro :: Literal -> [Clausula] -> [Clausula]
-- tal que (eliminaLiteralPuro l cs) es el conjunto obtenido eliminando
-- el literal puro l de cs. Por ejemplo,
--    eliminaLiteralPuro p [[p,q],[p,no q],[r,q],[r,no q]]
--    == [[r,q],[r,no q]]
--    eliminaLiteralPuro r [[r,q],[r,no q]]
--    == []
-- ---------------------------------------------------------------------

-- 1ª definición
eliminaLiteralPuro :: Literal -> [Clausula] -> [Clausula]
eliminaLiteralPuro l cs =
  [c | c <- cs, l `notElem` c]

-- 2ª definición
eliminaLiteralPuro2 :: Literal -> [Clausula] -> [Clausula]
eliminaLiteralPuro2 l =
  filter (l `notElem`)

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    literalesPuros :: [Clausula] -> [Literal]
-- tal que (literalesPuros s) es el conjunto de los literales puros de
-- s. Por ejemplo,
--    literalesPuros [[p,q],[p,no q],[r,q],[r,no q]]  ==  [p,r]
-- ---------------------------------------------------------------------

literalesPuros :: [Clausula] -> [Literal]
literalesPuros cs =
  [l | l <- literales cs, esLiteralPuro l cs]

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    eliminaLiteralesPuros :: [Clausula] -> [Clausula]
-- tal que (eliminaLiteralesPuros cs) es el conjunto obtenido aplicando a
-- cs el proceso de eliminación de literales puros. Por ejemplo,
--    eliminaLiteralesPuros [[p,q],[p,no q],[r,q],[r,no q]]
--    == []
--    eliminaLiteralesPuros [[p,q],[r,no s],[no r,s]]
--    == [[r,no s],[no r,s]]
-- ---------------------------------------------------------------------

eliminaLiteralesPuros :: [Clausula] -> [Clausula]
eliminaLiteralesPuros cs
  | null lp   = cs
  | otherwise = eliminaLiteralesPuros (eliminaLiteralPuro (head lp) cs)
  where lp = literalesPuros cs

-- ---------------------------------------------------------------------
-- § Bifurcación                                                      --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    bifurcacion :: [Clausula] -> Literal -> ([Clausula],[Clausula])
-- tal que (bifurcacion cs l) es la bifurcacion de cs según el literal
-- l. Por ejemplo,
--    bifurcacion [[p,no q],[no p,q],[q,no r],[no q,no r]] p
--    == ([[no q],[q,no r],[no q,no r]],[[q],[q,no r],[no q,no r]])
-- ---------------------------------------------------------------------

bifurcacion :: [Clausula] -> Literal -> ([Clausula],[Clausula])
bifurcacion cs l =
  ([delete l c  | c <- cs, l `elem` c]  ++ clausulas_sin_l_ni_l',
   [delete l' c | c <- cs, l' `elem` c] ++ clausulas_sin_l_ni_l')
  where l'                    = complementario l
        clausulas_sin_l_ni_l' = [c | c <- cs, l `notElem` c, l' `notElem` c]

-- ---------------------------------------------------------------------
-- § Algoritmo de inconsistencia de Davis y Putnam                    --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    tieneClausulasUnitarias :: [Clausula] -> Bool
-- tal que (tieneClausulasUnitarias cs) se verifica si cs tiene cláusulas
-- unitarias. Por ejemplo,
--    tieneClausulasUnitarias [[p,q],[p],[no q]]  ==  True
--    tieneClausulasUnitarias [[p,q],[p,no q]]    ==  False
-- ---------------------------------------------------------------------

tieneClausulasUnitarias :: [Clausula] -> Bool
tieneClausulasUnitarias cs =
  clausulaUnitaria cs /= Nothing

-- ---------------------------------------------------------------------
-- Ejercicio 14: Definir la función
--    tieneLiteralesPuros :: [Clausula] -> Bool
-- tal que (tieneLiteralesPuros cs) se verifica si cs tiene literales
-- puros. Por ejemplo,
--    tieneLiteralesPuros [[p,q],[p,no q],[r,q],[r,no q]]
--    == True
--    tieneLiteralesPuros [[p,q],[no p,no q],[no r,q],[r,no q]]
--    == False
-- ---------------------------------------------------------------------

tieneLiteralesPuros :: [Clausula] -> Bool
tieneLiteralesPuros cs =
  not (null (literalesPuros cs))

-- ---------------------------------------------------------------------
-- Ejercicio 15: Definir la función
--    esInconsistentePorDP :: [Clausula] -> Bool
-- tal que (esInconsistentePorDP cs) se verifica si cs es inconsistente
-- mediante el algoritmo de inconsistencia de Davis y Putnam. Por
-- ejemplo,
--    esInconsistentePorDP [[p,q],[p,q,no p]]
--    == False
--    esInconsistentePorDP [[p,q,no r],[p,no q],[no p],[r],[u]]
--    == True
--    esInconsistentePorDP [[p,q],[no q],[no p,q,no r]]
--    == False
--    esInconsistentePorDP [[no p,q],[p],[r,u]]
--    == False
--    esInconsistentePorDP [[p,q],[p,no q],[r,q],[r,no q]]
--    == False
--    esInconsistentePorDP [[p,q],[r,no s],[no r,s]]
--    == False
--    esInconsistentePorDP [[p,no q],[no p,q],[q,no r],[no q,no r]]
--    == False
--    esInconsistentePorDP [[p,q],[p,no q],[r,q],[r,no q]]
--    == False
-- ---------------------------------------------------------------------

esInconsistentePorDP :: [Clausula] -> Bool
esInconsistentePorDP cs =
  esInconsistentePorDP' (eliminaTautologias cs)

esInconsistentePorDP' :: [Clausula] -> Bool
esInconsistentePorDP' cs
  | null cs = False
  | [] `elem` cs = True
  | tieneClausulasUnitarias cs =
      esInconsistentePorDP' (eliminaClausulasUnitarias cs)
  | tieneLiteralesPuros cs =
      esInconsistentePorDP' (eliminaLiteralesPuros cs)
  | otherwise =
      esInconsistentePorDP' s1 && esInconsistentePorDP' s2
  where l       = head (head cs)
        (s1,s2) = bifurcacion cs l

-- ---------------------------------------------------------------------
-- § Decisión de validez mediante Davis y Putnam                      --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 16: Definir la función
--    esValidaPorDP :: Prop -> Bool
-- tal que (esValidaPorDP f) se verifica si f es válida mediante el
-- algoritmo de Davis y Putnam. Por ejemplo,
--    esValidaPorDP (p --> p)                 ==  True
--    esValidaPorDP ((p --> q) \/ (q --> p))  ==  True
--    esValidaPorDP (p --> q)                 ==  False
-- ---------------------------------------------------------------------

esValidaPorDP :: Prop -> Bool
esValidaPorDP f =
  esInconsistentePorDP (clausulas (Neg f))

-- ---------------------------------------------------------------------
-- § Decisión de consecuencia mediante Davis y Putnam                 --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 17: Definir la función
--    esConsecuenciaPorDP :: [Prop] -> Prop -> Bool
-- tal que (esConsecuenciaPorDP cs f) se verifica si f es consecuencia de
-- cs mediante el algoritmo de Davis y Putnam. Por ejemplo,
--    esConsecuenciaPorDP [p --> q, q --> r] (p --> r)  ==  True
--    esConsecuenciaPorDP [p] (p /\ q)  ==  False
-- ---------------------------------------------------------------------

esConsecuenciaPorDP :: [Prop] -> Prop -> Bool
esConsecuenciaPorDP cs f =
  esInconsistentePorDP (clausulasConjunto (Neg f : cs))
