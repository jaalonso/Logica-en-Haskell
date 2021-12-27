-- Secuentes.hs
-- Cálculo de secuentes proposicionales.
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module Secuentes where

-- ---------------------------------------------------------------------
-- § Introducción                                                     --
-- ---------------------------------------------------------------------

-- En este módulo se implementa el método de los secuentes
-- proposicionales siguiendo su exposición del capítulo 3.4 del libro de
-- Jean H. Gallier "Logic for computer science (Foundations of automatic
-- theorem proving)"

-- ---------------------------------------------------------------------
-- § Librerías auxiliares                                             --
-- ---------------------------------------------------------------------

import SintaxisSemantica
import Data.List
import Debug.Trace

-- ---------------------------------------------------------------------
-- § Secuentes                                                        --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir el tipo de datos Secuentes para representar los
-- secuentes como pares de listas de fórmulas.
--
-- Nota: El secuente
--    ([F1, F2,..., Fn],[G1, G2,..., Gn])
-- representa la fórmula
--    (F1 /\ F2 /\ ... /\ Fn) --> (G1 \/ G2 \/ ... \/ Gn)
-- ---------------------------------------------------------------------

type Secuente = ([Prop],[Prop])


-- Notaciones de secuentes:
-- + S1 ==> S2               representa a <S1,S2>.
-- + F1,...,Fn ==> G1,...,Gm representa a {F1,...,Fn} ==> {G1,...,Gm}
-- + S1,F ==> S2             representa a S1 U {F} ==> S2
-- + S1 ==> S2,F             representa a S1 ==> S2 U {F}
-- + ==> S                   representa a {} ==> S
-- + ==> F                   representa a {} ==> {F}

-- Nomenclatura de secuentes:
-- Sea F1,...,Fn ==> G1,...,Gm un secuente.
-- + {F1,...,Fn} es el antecente (o parte izquierda) del secuente
-- + {G1,...,Gm} es el consecuente (o parte derecha) del secuente
-- + F1,...,Fn son las hipótesis del secuente
-- + G1,...,Gm son los objetivos del secuente

-- ---------------------------------------------------------------------
-- § Axiomas y reglas de secuentes                                    --
-- ---------------------------------------------------------------------

-- + Axioma: S1, F ==>  S2, F.
--
-- + Reglas:
--   + De la negación:
--       S1 ==>  S2, F                 S1, F  ==> S2
--       ---------------  [Ino]        --------------  [Dno]
--       S1, no F ==> S2               S1 ==> S2,no F
--
--   + De la conjunción:
--      S1, F, G ==> S2                S1 ==> S2, F
--                                     S1 ==> S2, G
--      -----------------  [I/\]       ----------------- [D/\]
--      S1, F /\ G ==> S2              S1 ==> S2, F /\ G
--
--   + De la disyunción:
--      S1 ==> S2, F
--      S1 ==> S2, G                   S1 ==> S2, F, G
--      ----------------  [I\/]        -----------------  [D \/]
--      S1, F \/G ==> S2               S1 ==> S2, F \/ G
--
--   + De la implicación:
--      S1 ==> S2, F
--      S1, G ==> S2                   S1, F ==> S2, G
--      ------------------ [I-->]      ------------------  [D-->]
--      S1, F --> G ==> S2             S1 ==> S2, F --> G
--
--   + De la equivalencia:
--      S1, F, G ==> S2                S1, F ==> S2, G
--      S1 ==> S2, F, G                S1, G ==> S2, F
--      ------------------- [I<-->]    ------------------ [D<-->]
--      S1, F <--> G ==> S2            S1 ==> S2, F<--> G
--
-- + Elementos de un regla:
--   + Premisas: Los secuentes sobre la raya.
--   + Conclusión: El secuente bajo la raya.
--   + Nombre: Entre corchete (I indica izquierda y D derecha).

-- ---------------------------------------------------------------------
-- § Demostrabilidad por secuentes                                    --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir la función
--    esAxioma :: Secuente -> Bool
-- tal que (esAxioma s) se verifica si el secuente s es un axioma; es
-- decir, alguna fórmula de su parte derecha está en su parte
-- izquierda. Por ejemplo,
--    esAxioma ([p /\ q, r], [r --> q, p /\ q])  ==  True
--    esAxioma ([p /\ q, r], [r --> q, p, q])    ==  False
-- ---------------------------------------------------------------------

esAxioma :: Secuente -> Bool
esAxioma (i,d) =
  not (null (i `intersect` d))

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    reglaIzquierda :: Prop -> Secuente -> [Secuente]
-- tal que (reglaIzquierda f s) es el secuente obtenido aplicando a s la
-- regla izquierda correspondiente a la fórmula f. Por ejemplo,
--    reglaIzquierda (no p) ([no p, q],[r])
--    == [([q],[p,r])]
--    reglaIzquierda (p /\ q) ([r, p /\ q],[s])
--    == [([p,q,r],[s])]
--    reglaIzquierda (p \/ q) ([r, p \/ q],[s])
--    == [([p,r],[s]),([q,r],[s])]
--    reglaIzquierda (p --> q) ([r, p --> q],[s])
--    == [([r],[p,s]),([q,r],[s])]
--    reglaIzquierda (p <--> q) ([r, p <--> q],[s])
--    == [([p,q,r],[s]),([r],[p,q,s])]
-- ---------------------------------------------------------------------

reglaIzquierda :: Prop -> Secuente -> [Secuente]
reglaIzquierda f@(Neg f1)     (i,d) = [(delete f i,         f1:d)]
reglaIzquierda f@(Conj f1 f2) (i,d) = [(f1:f2 : delete f i, d)]
reglaIzquierda f@(Disj f1 f2) (i,d) = [(f1 : delete f i,    d),
                                       (f2 : delete f i,    d)]
reglaIzquierda f@(Impl f1 f2) (i,d) = [(delete f i,         f1:d),
                                       (f2 : delete f i,    d)]
reglaIzquierda f@(Equi f1 f2) (i,d) = [(f1:f2 : delete f i, d),
                                       (delete f i,         f1:f2:d)]
reglaIzquierda (Atom _) (_, _)      = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
--    reglaDerecha :: Prop -> Secuente -> [Secuente]
-- tal que (reglaDerecha f s) es el secuente obtenido aplicando a s la
-- regla derecha correspondiente a la fórmula f. Por ejemplo,
--    reglaDerecha (no p) ([q],[no p, r])
--    == [([p,q],[r])]
--    reglaDerecha (p /\ q) ([s],[p /\ q, r])
--    == [([s],[p,r]),([s],[q,r])]
--    reglaDerecha (p \/ q) ([s],[p \/ q, r])
--    == [([s],[p,q,r])]
--    reglaDerecha (p --> q) ([s],[p --> q, r])
--    == [([p,s],[q,r])]
--    reglaDerecha (p <--> q) ([s],[p <--> q, r])
--    == [([p,s],[q,r]),([q,s],[p,r])]
-- ---------------------------------------------------------------------

reglaDerecha :: Prop -> Secuente -> [Secuente]
reglaDerecha f@(Neg f1)     (i,d) = [(f1:i, delete f d)]
reglaDerecha f@(Conj f1 f2) (i,d) = [(i,    f1 : delete f d),
                                     (i,    f2 : delete f d)]
reglaDerecha f@(Disj f1 f2) (i,d) = [(i,    f1:f2 : delete f d)]
reglaDerecha f@(Impl f1 f2) (i,d) = [(f1:i, f2 : delete f d)]
reglaDerecha f@(Equi f1 f2) (i,d) = [(f1:i, f2 : delete f d),
                                     (f2:i, f1 : delete f d)]
reglaDerecha (Atom _) (_, _)      = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    esAtomica :: Prop -> Bool
-- tal que (esAtomica f) se verifica si la fórmula f es atómica. Por
-- ejemplo,
--    esAtomica p         ==  True
--    esAtomica (p /\ q)  ==  False
-- ---------------------------------------------------------------------

esAtomica :: Prop -> Bool
esAtomica (Atom _) = True
esAtomica _        = False

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir la función
--    compuestasIzquierda :: Secuente -> [Prop]
-- tal que (compuestasIzquierda s) es la lista de las fórmulas
-- compuestas en la parte izquierda del secuente s. Por ejemplo,
--    compuestasIzquierda ([no p, q, r /\ s],[no q])
--    == [no p,(r /\ s)]
-- ---------------------------------------------------------------------

-- 1ª definición
compuestasIzquierda :: Secuente -> [Prop]
compuestasIzquierda (i,_) =
  [f | f <- i, not (esAtomica f)]

-- 2ª definición
compuestasIzquierda2 :: Secuente -> [Prop]
compuestasIzquierda2 (i,_) =
  filter (not . esAtomica) i

-- 3ª definición
compuestasIzquierda3 :: Secuente -> [Prop]
compuestasIzquierda3 =
  filter (not . esAtomica) . fst

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir la función
--    compuestasDerecha :: Secuente -> [Prop]
-- tal que (compuestasDerecha s) es la lista de las fórmulas
-- compuestas en la parte derecha del secuente s. Por ejemplo,
--    compuestasDerecha ([no p, q, r /\ s],[no q, s --> p, r])
--    == [no q,(s --> p)]
-- ---------------------------------------------------------------------

-- 1ª definición
compuestasDerecha :: Secuente -> [Prop]
compuestasDerecha (_,d) =
  [f | f <- d, not (esAtomica f)]

-- 2ª definición
compuestasDerecha2 :: Secuente -> [Prop]
compuestasDerecha2 (_,d) =
  filter (not . esAtomica ) d

-- 3ª definición
compuestasDerecha3 :: Secuente -> [Prop]
compuestasDerecha3 =
  filter (not . esAtomica) . snd

-- + Un árbol es una demostración por secuentes si:
--   (1) las hojas son axiomas;
--   (2) si S1 ==> S2 es un nodo con hijos, entonces sus hijos son las premisas
--       de una regla y el nodo es la conclusión.
--
-- + Un secuente S1 ==> S2 es demostrable si existe un árbol de
--   demostración por secuentes cuya raiz es S1 ==> S2.
--
-- + El procedimiento para determinar si S1 ==> S2 es probable es
--   + Si S1 ==> S2 es un axioma, entonces es probable.
--   + Si S1 tiene fórmulas compuestas, sea F la primera de dichas fórmulas y
--     verificar la probabilidad de los secuentes resultantes de aplicar a F la
--     correspondiente regla izquierda.
--   + Si S2 tiene fórmulas compuestas, sea F la primera de dichas fórmulas y
--     verificar la probabilidad de los secuentes resultantes de aplicar a F la
--     correspondiente regla derecha.
--   + En caso cotrario, no es probable.

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    esProbablePorSecuentes' :: Secuente -> Bool
-- tal que (esProbablePorSecuentes' s) se verifica si s es probable. Por
-- ejemplo,
--    esProbablePorSecuentes' ([p --> q, q --> r],[p --> r])   ==  True
--    esProbablePorSecuentes' ([p --> q, q --> r],[p <--> r])  ==  False
--    esProbablePorSecuentes' ([],[p --> p])                   ==  True
--    esProbablePorSecuentes' ([p /\ no(p)],[])                ==  True
-- ---------------------------------------------------------------------

esProbablePorSecuentes' :: Secuente -> Bool
esProbablePorSecuentes' sec
  | esAxioma sec = True
  | not (null compuestasI) =
      sonProbalesPorSecuentes (reglaIzquierda (head compuestasI) sec)
  | not (null compuestasD) =
      sonProbalesPorSecuentes (reglaDerecha (head compuestasD) sec)
  | otherwise = False
  where compuestasI = compuestasIzquierda sec
        compuestasD = compuestasDerecha sec

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    sonProbalesPorSecuentes :: [Secuente] -> Bool
-- tal que (sonProbalesPorSecuentes ss) se verifica si los secuentes de
-- ss son probables. Por ejemplo,
--    sonProbalesPorSecuentes [([],[q,p,(p --> r)]),([r],[p,(p --> r)])]
--    == True
-- ---------------------------------------------------------------------

-- 1ª definición
sonProbalesPorSecuentes :: [Secuente] -> Bool
sonProbalesPorSecuentes ss =
  and [esProbablePorSecuentes' sec | sec <- ss]

-- 2ª definición
sonProbalesPorSecuentes2 :: [Secuente] -> Bool
sonProbalesPorSecuentes2 =
  all esProbablePorSecuentes'

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    esProbablePorSecuentes :: Prop -> Bool
-- tal que (esProbablePorSecuentes f) se verifica si la fórmula f es
-- probable mediante secuentes. Por ejemplo,
--    esProbablePorSecuentes ((p --> q) \/ (q --> p))  ==  True
--    esProbablePorSecuentes (p --> q)                 ==  False
-- ---------------------------------------------------------------------

esProbablePorSecuentes :: Prop -> Bool
esProbablePorSecuentes f =
  esProbablePorSecuentes' ([],[f])

-- ---------------------------------------------------------------------
-- § Prueba por secuentes                                             --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    marcas :: Int -> String
-- tal que (marcas n) es la cadena correspondiente a n marcas. Por
-- ejemplo,
--    > marcas 3
--    " ||| "
-- ---------------------------------------------------------------------

marcas :: Int -> String
marcas  n =
  " " ++ replicate n '|' ++ " "

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    pruebaPorSecuentes' :: Secuente -> Int -> Bool
-- tal que (pruebaPorSecuentes' s) escribe la prueba por secuentes de
-- s. Por ejemplo,
--    λ> pruebaPorSecuentes' ([p --> q, q --> r],[p --> r]) 1
--     | [(p --> q),(q --> r)] ==> [(p --> r)]
--     || [(q --> r)] ==> [p,(p --> r)]
--     ||| [] ==> [q,p,(p --> r)]
--     ||| [p] ==> [r,q,p]
--     ||| [r] ==> [p,(p --> r)]
--     ||| [p,r] ==> [r,p]
--     || [q,(q --> r)] ==> [(p --> r)]
--     ||| [q] ==> [q,(p --> r)]
--     ||| [r,q] ==> [(p --> r)]
--     ||| [p,r,q] ==> [r]
--    True
-- ---------------------------------------------------------------------

pruebaPorSecuentes' :: Secuente -> Int -> Bool
pruebaPorSecuentes' (i,d) n
  | trace (marcas n ++ show i ++ " ==> " ++ show d) False = undefined
pruebaPorSecuentes' sec n
  | esAxioma sec = True
  | compuestasI /= [] =
      pruebasPorSecuentes' (reglaIzquierda (head compuestasI) sec) n
  | compuestasD /= [] =
      pruebasPorSecuentes' (reglaDerecha (head compuestasD) sec) n
  | otherwise = False
  where compuestasI = compuestasIzquierda sec
        compuestasD = compuestasDerecha sec

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    pruebasPorSecuentes' :: [Secuente] -> Int -> Bool
-- tal que (pruebasPorSecuentes' ss) escribe las pruebas por secuentes
-- de ss. Por ejemplo,
--    λ> pruebasPorSecuentes' [([],[q,p,(p --> r)]),([r],[p,(p --> r)])] 1
--     || [] ==> [q,p,(p --> r)]
--     || [p] ==> [r,q,p]
--     || [r] ==> [p,(p --> r)]
--     || [p,r] ==> [r,p]
--    True
-- ---------------------------------------------------------------------

pruebasPorSecuentes' :: [Secuente] -> Int -> Bool
pruebasPorSecuentes' [sec] n =
  pruebaPorSecuentes' sec n
pruebasPorSecuentes' ss n =
  and [pruebaPorSecuentes' sec (n+1) | sec <- ss]

-- ---------------------------------------------------------------------
-- Ejercicio 14: Definir la función
--    pruebaPorSecuentes :: Prop -> Bool
-- tal que (pruebaPorSecuentes f) escribe las pruebas por secuentes de
-- la fórmula f. Por ejemplo,
-- λ> pruebaPorSecuentes ((p --> q) /\ (q --> r) --> (p --> r))
--  | [] ==> [(((p --> q) /\ (q --> r)) --> (p --> r))]
--  | [((p --> q) /\ (q --> r))] ==> [(p --> r)]
--  | [(p --> q),(q --> r)] ==> [(p --> r)]
--  || [(q --> r)] ==> [p,(p --> r)]
--  ||| [] ==> [q,p,(p --> r)]
--  ||| [p] ==> [r,q,p]
--  ||| [r] ==> [p,(p --> r)]
--  ||| [p,r] ==> [r,p]
--  || [q,(q --> r)] ==> [(p --> r)]
--  ||| [q] ==> [q,(p --> r)]
--  ||| [r,q] ==> [(p --> r)]
--  ||| [p,r,q] ==> [r]
-- True
-- λ> pruebaPorSecuentes ((p --> q) /\ (q --> r) --> (p --> s))
--  | [] ==> [(((p --> q) /\ (q --> r)) --> (p --> s))]
--  | [((p --> q) /\ (q --> r))] ==> [(p --> s)]
--  | [(p --> q),(q --> r)] ==> [(p --> s)]
--  || [(q --> r)] ==> [p,(p --> s)]
--  ||| [] ==> [q,p,(p --> s)]
--  ||| [p] ==> [s,q,p]
--  ||| [r] ==> [p,(p --> s)]
--  ||| [p,r] ==> [s,p]
--  || [q,(q --> r)] ==> [(p --> s)]
--  ||| [q] ==> [q,(p --> s)]
--  ||| [r,q] ==> [(p --> s)]
--  ||| [p,r,q] ==> [s]
-- False
-- ---------------------------------------------------------------------

pruebaPorSecuentes :: Prop -> Bool
pruebaPorSecuentes f =
  pruebaPorSecuentes' ([],[f]) 1

-- ---------------------------------------------------------------------
-- § Deducción por secuentes                                          --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 15: Definir la función
--    esDeduciblePorSecuentes :: [Prop] -> Prop -> Bool
-- tal que (esDeduciblePorSecuentes s f) se verifica si la fórmula f es
-- deducible por secuentes a partir de s. Por ejemplo,
--    esDeduciblePorSecuentes [p --> q, q --> r] (p --> r)
--    == True
--    esDeduciblePorSecuentes [p --> q, q --> r] (p <--> r)
--    == False
-- ---------------------------------------------------------------------

esDeduciblePorSecuentes :: [Prop] -> Prop -> Bool
esDeduciblePorSecuentes fs g =
  esProbablePorSecuentes' (fs,[g])

-- ---------------------------------------------------------------------
-- Ejercicio 16: Definir la función
--    deduccionPorSecuentes  :: [Prop] -> Prop -> Bool
-- tal que (deduccionPorSecuentes s f) escribe la deducción por
-- secuentes de la fórmula f a partir del conjunto de fórmulas s. Por
-- ejemplo,
--    λ> deduccionPorSecuentes [p --> q, q --> r] (p --> r)
--     | [(p --> q),(q --> r)] ==> [(p --> r)]
--     || [(q --> r)] ==> [p,(p --> r)]
--     ||| [] ==> [q,p,(p --> r)]
--     ||| [p] ==> [r,q,p]
--     ||| [r] ==> [p,(p --> r)]
--     ||| [p,r] ==> [r,p]
--     || [q,(q --> r)] ==> [(p --> r)]
--     ||| [q] ==> [q,(p --> r)]
--     ||| [r,q] ==> [(p --> r)]
--     ||| [p,r,q] ==> [r]
--    True
-- ---------------------------------------------------------------------

deduccionPorSecuentes  :: [Prop] -> Prop -> Bool
deduccionPorSecuentes fs g =
  pruebaPorSecuentes'  (fs,[g]) 1
