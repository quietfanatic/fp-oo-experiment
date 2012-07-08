
import Unsafe.Coerce
import qualified GHC.Prim

import qualified Text.ParserCombinators.ReadP as P
import Data.Char
import Data.List
import System.Environment

ptreq x y = 1# GHC.Prim.==# GHC.Prim.reallyUnsafePtrEquality# x y
-- UTIL

parens = ("(" ++) . (++ ")")

join sep [] = []
join sep (p:[]) = p
join sep (p:ps) = p ++ sep ++ join sep ps

compfst a b = compare (fst a) (fst b)

a // b = case a of
    Just a -> a
    Nothing -> b

mapsnd f = map (\(a, b) -> (a, f b))
for = flip map
forsnd = flip mapsnd

-- TYPES

type Any = GHC.Prim.Any

hide :: a -> Any
hide = unsafeCoerce
hidef :: (a -> b) -> Any -> Any
hidef = unsafeCoerce
hideff :: (a -> b -> c) -> Any -> Any -> Any
hideff = unsafeCoerce

unhide :: Any -> a
unhide = unsafeCoerce
unhidef :: (Any -> Any) -> a -> b
unhidef = unsafeCoerce

data Type = T_Type
          | T_Thing
          | T_int
          | T_Func !Type !Type
          | T_Err
          | T_Obj [(String, (Type, Any -> Any))] -- sorted
          | T_Interface [(String, Type)] -- sorted

show_Type x = case x of
    T_Type -> "Type"
    T_Thing -> "Thing"
    T_int -> "int"
    T_Err -> "Err"
    T_Func i o -> "Func " ++ showp_Type i ++ " " ++ showp_Type o
    T_Obj mems -> "<Object>"
    T_Interface mems -> "{" ++ join "; " (map (\(n, t) -> n ++ " : " ++ show_Type t) mems) ++ "}"
    _ -> "<???>"
showp_Type x = case x of
    T_Func _ _ -> parens (show_Type x)
    _ -> show_Type x

-- Frequent error messages
convert_error f t = "Cannot convert " ++ show_Type f ++ " to " ++ show_Type t
apply_error f t = "Cannot apply " ++ show_Type f ++ " to " ++ show_Type t

-- INTERFACE

data Interface = Interface ![Any -> Any] !Any

-- THING

data Thing = Thing !Type !Any

show_Thing x = case x of
    Thing T_Type a -> show_Type (unhide a)
    Thing T_Thing a -> show_Thing (unhide a)
    Thing T_int a -> show (unhide a :: Int)
    Thing T_Err a -> "<Error: " ++ unhide a ++ ">"
    Thing t a -> case name_reverse_lookup a builtins of
        Just n -> "<" ++ n ++ ">"
        Nothing -> "<" ++ show_Type t ++ ">"

int_Thing :: Int -> Thing
int_Thing = Thing T_int . hide

err_Thing :: String -> Thing
err_Thing = Thing T_Err . hide

-- CONVERSION

convert :: Type -> Type -> Maybe (Any -> Any)
convert T_Type T_Type = Just $ hidef id
convert T_Thing T_Thing = Just $ hidef id
convert T_int T_int = Just $ hidef id
convert T_Err T_Err = Just $ hidef id
convert (T_Func fromi fromo) (T_Func toi too) = do
    convi <- convert toi fromi
    convo <- convert fromo too
    return $ hidef (\f -> convo . f . convi)
convert (T_Obj objmems) (T_Interface ifmems) =
    let build_vtable _ [] = Just []
        build_vtable [] _ = Nothing
        build_vtable (om:oms) (im:ims) =
            case compfst om im of
                LT -> build_vtable oms (im:ims)
                GT -> Nothing
                EQ -> do
                    conv <- convert (fst (snd om)) (snd im)
                    rest <- build_vtable oms ims
                    return $ conv . snd (snd om) : rest
    in do
        vtable <- build_vtable objmems ifmems
        return $ hidef (\obj -> Interface vtable obj)
convert (T_Interface frommems) (T_Interface tomems) =
    let bb_vtable fromi _ [] = Just (\fvt -> [])
        bb_vtable fromi [] _ = Nothing
        bb_vtable fromi (fm:fms) (tm:tms) =
            case compfst fm tm of
                LT -> bb_vtable (fromi + 1) fms (tm:tms)
                GT -> Nothing
                EQ -> do
                    conv <- convert (snd fm) (snd tm)
                    build_rest <- bb_vtable (fromi + 1) fms tms
                    return $ (\fvt -> build_rest fvt ++ [conv . (fvt!!fromi)])
    in do
        b_vtable <- bb_vtable 0 frommems tomems
        return $ hidef (\(Interface vt a) -> Interface (b_vtable vt) a)
convert from T_Thing = return $ hidef (Thing from)
convert T_Thing to = Just $ hidef $
    (\(Thing from a) -> ensure_convert from to a)
convert _ _ = Nothing

ensure_convert f t = convert f t // error (convert_error f t)

apply :: Type -> Type -> Maybe (Type, Any -> Any -> Any)
apply T_Type _ = Nothing
apply T_Thing argt = Just (T_Thing,
    (\f arg -> let Thing ft fa = unhide f
                   (ot, app) = ensure_apply ft argt
               in hide (Thing ot (app fa arg))
    ))
apply T_int _ = Nothing
apply T_Err _ = Just (T_Err, hideff const)
apply (T_Func i o) t = case convert t i of
    Just conv -> Just (o, hideff (. conv))
    Nothing -> case t of
        T_Err -> Just (T_Err, hideff (flip const))
        _ -> Nothing
apply _ _ = Nothing

ensure_apply f t = apply f t // error (apply_error f t)


-- TYPED EXPR

data Expr = E_Thing !Thing
          | E_app !Expr !Expr
          | E_lambda !Expr !Expr
          | E_param
          | E_this
          | E_pop !Expr
          | E_object ![(String, Expr)] -- sorted
          | E_member !Expr !String
          | E_interface ![(String, Expr)]
          | E_cond !Expr !Expr !Expr

err_Expr :: String -> Expr
err_Expr = E_Thing . Thing T_Err . hide

show_Expr x = case x of
    E_Thing t -> show_Thing t
    E_app f arg -> showpl_Expr f ++ " " ++ showp_Expr arg
    E_lambda t body -> "_ : " ++ show_Expr t ++ " -> " ++ show_Expr body
    E_param -> "_"
    E_this -> ""
    E_pop e -> "^" ++ showp_Expr e
    E_object mems -> "{" ++ join "; " (map (\(n, e) -> n ++ " = " ++ show_Expr e) mems) ++ "}"
    E_member e m -> showp_Expr e ++ "." ++ m
    E_interface mems -> "{" ++ join "; " (map (\(n, e) -> n ++ " : " ++ show_Expr e) mems) ++ "}"
    E_cond c t e -> "(" ++ show_Expr c ++ " ?? " ++ show_Expr t ++ " !! " ++ show_Expr e ++ ")"
    _ -> "<???>"
showp_Expr x = case x of
    E_app _ _ -> parens (show_Expr x)
    E_lambda _ _ -> parens (show_Expr x)
    E_pop _ -> parens (show_Expr x)
    _ -> show_Expr x
showpl_Expr x = case x of
    E_lambda _ _ -> showp_Expr x
    _ -> show_Expr x

eval_Expr :: Expr -> [Thing] -> Thing
eval_Expr x env = case x of
    E_Thing t -> t
    E_app f arg ->
        let Thing ft fa = eval_Expr f env
            Thing argt arga = eval_Expr arg env
        in case apply ft argt of
            Just (ot, f) -> Thing ot (f fa arga)
            Nothing -> case ft of
                T_Err -> Thing ft fa
                _ -> err_Thing (convert_error ft argt)
    E_lambda typ_e body ->
        let Thing typetype x = eval_Expr typ_e env
        in case convert typetype T_Type of
            Just conv ->
                Thing (T_Func (unhide (conv x)) T_Thing)
                      (hide (\param -> eval_Expr body (Thing (unhide (conv x)) param : env)))
            Nothing -> case typetype of
                T_Err -> Thing typetype x
                _ -> err_Thing (convert_error typetype T_Type)
    E_param -> head env
    E_pop e -> eval_Expr e (tail env)
    E_object mems ->
        let objtype = T_Obj omems
            omems = forsnd mems
                (\e -> (T_Thing, hidef (\param -> eval_Expr e (Thing objtype param : env))))
        in Thing objtype (hide env)
    E_member e name ->
        let Thing typ obj = eval_Expr e env
        in case convert typ (T_Interface [(name, T_Thing)]) of
            Just conv ->
                let (Interface [f] a) = unhide (conv obj)
                in unhide (f a)
            Nothing -> case typ of
                T_Err -> Thing typ obj
                _ -> err_Thing $ "Type " ++ show_Type typ ++ " has no member " ++ name
    E_interface mems -> 
        let iftype = T_Interface imems
            imems = forsnd mems (\e ->
                let Thing t a = eval_Expr e env
                in case convert t T_Type of
                    Just conv -> unhide (conv a) :: Type
                    Nothing -> error (convert_error t T_Type))
        in Thing T_Type (hide (T_Interface imems))
    E_cond c t e ->
        let Thing ctype ca = eval_Expr c env
        in case convert ctype T_int of
            Just conv -> if (unhide (conv ca) :: Int) /= 0 then eval_Expr t env else eval_Expr e env
            Nothing -> err_Thing (convert_error ctype T_int)

-- AST

data AST = AST_int !Int
         | AST_Thing !Thing
         | AST_id !String
         | AST_app !AST !AST
         | AST_lambda !String !AST !AST
         | AST_object ![(String, AST)] -- not sorted
         | AST_member !AST !String
         | AST_interface ![(String, AST)]
         | AST_cond !AST !AST !AST
         | AST_err !String

show_AST x = case x of
    AST_int i -> show i
    AST_Thing t -> show_Thing t
    AST_id name -> name
    AST_err mess -> "<Error: " ++ mess ++ ">"
    AST_app f arg -> showpl_AST f ++ " " ++ showp_AST arg
    AST_lambda param typ body -> param ++ " : " ++ show_AST typ ++ " -> " ++ show_AST body
    AST_object mems -> "{" ++ join "; " (map (\(n, a) -> n ++ " = " ++ show_AST a) mems) ++ "}"
    AST_member a name -> showp_AST a ++ "." ++ name
    AST_interface mems -> "{" ++ join "; " (map (\(n, a) -> n ++ " : " ++ show_AST a) mems) ++ "}"
    AST_cond c t e -> "(" ++ show_AST c ++ " ?? " ++ show_AST t ++ " !! " ++ show_AST e ++ ")"
    _ -> "<???>"
showp_AST x = case x of
    AST_app _ _ -> parens (show_AST x)
    AST_lambda _ _ _ -> parens (show_AST x)
    _ -> show_AST x
showpl_AST x = case x of
    AST_lambda _ _ _ -> showp_AST x
    _ -> show_AST x

lookup_id name [] = Nothing
lookup_id name (scope:scopes) =
    if elem name scope
        then Just (E_member E_param name)
        else lookup_id name scopes >>= (return . E_pop)

_AST_to_Expr :: AST -> [[String]] -> Expr
_AST_to_Expr x names = case x of
    AST_int i -> E_Thing (int_Thing i)
    AST_Thing t -> E_Thing t
    AST_id name -> case lookup_id name names of
        Nothing -> err_Expr $ "Unknown name: " ++ name
        Just expr -> expr
    AST_app f arg -> E_app (_AST_to_Expr f names) (_AST_to_Expr arg names)
    AST_lambda param typ body ->
        E_lambda (_AST_to_Expr typ names)
                 (_AST_to_Expr body ([param]:names))
    AST_object mems ->
        let new_names = map fst mems : names
            exprmems = mapsnd (\a -> _AST_to_Expr a new_names) mems
            sorted = sortBy compfst exprmems
        in E_object sorted
    AST_member a name -> E_member (_AST_to_Expr a names) name
    AST_interface mems ->
        let exprmems = mapsnd (\a -> _AST_to_Expr a names) mems
            sorted = sortBy compfst exprmems
        in E_interface sorted
    AST_cond c t e -> E_cond (_AST_to_Expr c names) (_AST_to_Expr t names) (_AST_to_Expr e names)
    AST_err mess -> err_Expr mess

-- PARSING

ws = P.skipSpaces
wordchar c = isAlphaNum c || c == '_'
alpha_ c = wordchar c && not (isDigit c)

parse_ident = do
    c <- P.satisfy alpha_
    s <- P.munch wordchar
    return $ c:s

parse_id = fmap AST_id parse_ident

parse_int = do
    c <- P.satisfy isDigit
    s <- P.munch isDigit
    return $ AST_int (read (c:s))

parse_parens = P.between (P.char '(') (ws >> P.char ')') parse_expr

parse_object = P.between (P.char '{') (ws >> P.char '}') parse_members

parse_interface = P.between (P.char '{') (ws >> P.char '}') parse_imembers

parse_members = do
    ws
    mems <- P.sepBy parse_objmember (P.skipMany1 (ws >> P.char ';'))
    P.skipMany (ws >> P.char ';')
    return $ AST_object mems

parse_imembers = do
    ws
    mems <- P.sepBy parse_imember (P.skipMany1 (ws >> P.char ';'))
    P.skipMany (ws >> P.char ';')
    return $ AST_interface mems

parse_objmember = do
    ws
    name <- parse_ident
    ws
    P.char '='
    ws
    def <- parse_expr
    return $ (name, def)

parse_imember = do
    ws
    name <- parse_ident
    ws
    P.char ':'
    ws
    typ <- parse_expr
    return $ (name, typ)

parse_expr = parse_lambda P.+++ parse_cond P.+++ parse_apps

parse_apps = do
    units <- P.many (ws >> parse_unit)
    return (case units of
        [] -> AST_err "Empty expression is not allowed"
        u:us -> foldl AST_app u us)

parse_lambda = do
    ws
    param <- parse_ident
    ws
    P.char ':'
    ws
    typ <- parse_expr
    ws
    P.string "->"
    body <- parse_expr
    return $ AST_lambda param typ body

parse_cond = do
    ws
    P.char '?'
    c <- parse_expr
    ws
    P.string "??"
    t <- parse_expr
    ws
    P.string "!!"
    e <- parse_expr
    return $ AST_cond c t e

parse_base = parse_id P.+++ parse_int P.+++ parse_parens P.+++ parse_object P.+++ parse_interface

parse_unit = do
    base <- parse_base
    mem_refs <- P.many parse_mem
    return $ foldl AST_member base mem_refs

parse_mem = P.char '.' >> parse_ident


parse_ast = do
    res <- parse_expr
    ws
    P.eof
    return res

parse_objectfile = do
    res <- parse_members
    ws
    P.eof
    return res

parse :: String -> AST
parse s =
    case P.readP_to_S parse_ast s of
        [] -> AST_err "Syntax error"
        (res, []):_ -> res
        (res, x):_ -> AST_err $ "Parser did not correctly read eof; leftover was: " ++ x

parse_file f = do
    file <- readFile f
    return (case P.readP_to_S parse_objectfile file of
        [] -> AST_err ("Syntax error in file: " ++ f)
        (res, []):_ -> res
        (res, x):_ -> AST_err $ "Parser did not correctly read eof")

-- BUILTINS


builtins =
    [
        ("add", E_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (+)))),
        ("sub", E_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (-)))),
        ("mul", E_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (*)))),
        ("int", E_Thing (Thing T_Type (hide (T_int)))),
		("Func", E_Thing (Thing (T_Func T_Type (T_Func T_Type T_Type)) (hide T_Func))),
        ("Thing", E_Thing (Thing T_Type (hide T_Thing))),
        ("Type", E_Thing (Thing T_Type (hide T_Type)))
    ]

wrap_environment program = AST_member
    (AST_object [
        ("main", program),
        ("add", AST_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (+)))),
        ("sub", AST_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (-)))),
        ("mul", AST_Thing (Thing (T_Func T_int (T_Func T_int T_int)) (hide (*)))),
        ("int", AST_Thing (Thing T_Type (hide T_int))),
        ("Thing", AST_Thing (Thing T_Type (hide T_Thing))),
        ("Type", AST_Thing (Thing T_Type (hide T_Type))),
        ("Func", AST_Thing (Thing (T_Func T_Type (T_Func T_Type T_Type)) (hide T_Func)))
    ]) "main"

name_reverse_lookup p [] = Nothing
name_reverse_lookup p ((name, E_Thing (Thing _ a)) : rest) =
    if ptreq a p then Just name else name_reverse_lookup p rest
name_reverse_lookup p (_:rest) = name_reverse_lookup p rest

str_to_Expr :: String -> Expr
str_to_Expr = flip _AST_to_Expr [] . wrap_environment . parse
file_to_Expr :: String -> IO Expr
file_to_Expr = fmap (flip _AST_to_Expr [] . wrap_environment) . parse_file

-- TESTING

test str expect = do
    putStrLn $ "S: " ++ str
    let ast = parse str
    putStrLn $ "A: " ++ show_AST ast
    let expr = _AST_to_Expr (wrap_environment ast) []
    program <- case expr of
        E_member (E_object fields) "main" -> case lookup "main" fields of
            Just f -> return f
            Nothing -> return $ error "That's weird, the predefined environment is wrong."
        _ -> return expr
    putStrLn $ "E: " ++ show_Expr program
    let res = eval_Expr expr []
    putStrLn $ " R: " ++ show_Thing res ++ " == " ++ show_Thing expect


do_some_testing = do
    test "3" $ int_Thing 3
    test "add" $ let E_Thing t = snd (head builtins) in t
    test "add 4 5" $ int_Thing 9
    test "add (add 5 (add 4 3)) (add (add 2 1) 0)" $ int_Thing 15
    test "(add 4) (5)" $ int_Thing 9
    test "int" $ Thing T_Type (hide T_int)
    test "x : int -> x" $ Thing (T_Func T_int T_int) (hide 0)
    test "(x : int -> x) 3" $ int_Thing 3
    test "(x : int -> add 4 x) 3" $ int_Thing 7
    test "(f : Func int int -> f 3) (x : int -> add 5 x)" $ int_Thing 8
    test "(f : Func int (Func int int) -> f 3 4) add" $ int_Thing 7
    test "(f : Func int int -> f 3)" $ Thing (T_Func (T_Func T_int T_int) T_Thing) (hide 0)
    test "3.xyz" $ err_Thing ""
    test "{x = 3; y = 4}" $ int_Thing (-99)
    test "{x = 3; y = 4}.x" $ int_Thing 3
    test "{x = 3; y = 4}.y" $ int_Thing 4
    test "((z : int -> {x = z; y = 6}) 7).x" $ int_Thing 7
    test "{o = {i = 9}}.o.i" $ int_Thing 9
    test "{double = x : int -> add x x}.double 5" $ int_Thing 10
    test "{Math = {double = x : int -> add x x}; main = Math.double 23}.main" $ int_Thing 46
    test "{Math = {inc_double = x : int -> add (add x inc) x; inc = 2}; main = Math.inc_double 23}.main" $ int_Thing 48
    test "{Math = bias : int -> {double_ = x : int -> add x x; bias_func = f : Func int int -> x : int -> add bias (f x); double = bias_func double_}; mymath = Math 1; main = mymath.double 10}.main" $ int_Thing 21
    test "{succ = add 1; nats_from = x:int->{ head = x; tail = nats_from (succ x) }; nats = nats_from 0; main = nats.tail.tail.tail.tail.tail.head}.main" $ int_Thing 5
    test "{Vec = x_:int -> y_:int -> {x=x_; y=y_}; dot = a:Thing -> b:Thing -> add (mul a.x b.x) (mul a.y b.y); main = dot (Vec 3 4) (Vec 2 5)}.main" $ int_Thing 26
    test "{x : int; y : int}" $ int_Thing 0
    test "{vec = x_:int -> y_:int -> {x=x_; y=y_}; Vec = {x:int; y:int}; dot = a:Vec -> b:Vec -> add (mul a.x b.x) (mul a.y b.y); main = dot (vec 3 4) (vec 2 10)}.main" $ int_Thing 46
    test "? 1 ?? 2 !! 3" $ int_Thing 2
    test "{fac = x:int -> ? x ?? mul x (fac (sub x 1)) !! 1}.fac 6" $ int_Thing 720
    test "{outer_rec = rec; rec = {rec = outer_rec}}.rec.rec" $ int_Thing 0

run_file args = do
    let file = head args
    obj <- if file == "-"
        then fmap str_to_Expr getContents
        else file_to_Expr file
    let program = E_member obj "main"
        prog_args = map str_to_Expr (tail args)
        real_program = foldl E_app program prog_args
        result = eval_Expr real_program []
    putStrLn $ show_Thing result

main = do
    args <- getArgs
    if null args
        then do_some_testing
        else run_file args







