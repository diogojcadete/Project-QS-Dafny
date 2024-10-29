datatype uop = Neg
datatype bop = Plus | Minus
datatype aexpr =
Var ( seq < nat >)
| Val ( nat )
| UnOp ( uop , aexpr )
| BinOp ( bop , aexpr , aexpr )

datatype code = VarCode ( seq < nat >) | ValCode ( nat ) | UnOpCode ( uop ) | BinOpCode ( bop )

function Serialize ( a : aexpr ) : seq < code >
{
    match a {
        case Var ( s ) => [ VarCode ( s ) ]
        case Val ( i ) => [ ValCode ( i ) ] 
        case UnOp ( op , a1 ) => Serialize ( a1 )+[ UnOpCode ( op )]
        case BinOp ( op , a1 , a2 ) => Serialize ( a2 )+ Serialize ( a1 )+[ BinOpCode ( op )]
    }
}


function Deserialize(cs: seq<code>) : seq<aexpr>
{
    DeserializeAux(cs, [])
}



function DeserializeAux(cs: seq<code>, es:seq<aexpr>): seq<aexpr>
    decreases cs
{
    if |cs| == 0 
        then es
    else 
        DeserializeAux(cs[1..], DeserializeCode(cs[0], es))
}

function DeserializeCode(cd: code, es : seq<aexpr>): seq<aexpr> 
{
    match cd {
        case VarCode ( s ) => [ Var (s) ] + es
        
        case ValCode ( i ) => [ Val (i) ] + es

        case UnOpCode ( uop ) => 
            if |es| < 1 then [ ] 
            else [ UnOp ( uop , es[0] ) ] + es[1..]
        
        case BinOpCode ( bop ) => 
            if |es| < 2 then [ ] 
            else [ BinOp ( bop , es[0] , es[1]) ] + es[2..]
    }   
}

//1.2

//Deserialize(Serialise(a)) == [a] its not an inductive case
//DeserializeAux(Serialize(ae) + cds, es) == DeserializeAux(cds, [ae] + es)

lemma DeserializeInverseOfSerialize1(ae : aexpr, cds: seq<code>, es : seq<aexpr>)
    ensures DeserializeAux(Serialize(ae) + cds, es) == DeserializeAux(cds, [ae] + es){

    match ae{
        case Var ( s ) => 
            calc {
                DeserializeAux(Serialize(ae) + cds, es);
                == // by case
                DeserializeAux(Serialize(Var ( s )) + cds, es);
                == // by definition of Serialize
                DeserializeAux([ VarCode ( s ) ] + cds, es);
                == // by definition of Deserialize  
                DeserializeAux(cds, DeserializeCode(VarCode ( s ), es)); 
                ==  
                DeserializeAux(cds, [ Var ( s ) ] + es);
                
            }
        
        case Val ( i ) =>
            calc {
                DeserializeAux(Serialize(ae) + cds, es);
                == // by case
                DeserializeAux(Serialize(Val ( i )) + cds, es);
                == // by definition of Serialize
                DeserializeAux([ ValCode ( i ) ] + cds, es);
                == // by definition of Deserialize
                DeserializeAux(cds, DeserializeCode(ValCode ( i ), es));
                ==
                DeserializeAux(cds, [ Val ( i ) ] + es);
                ==
                DeserializeAux(cds, [ ae ] + es);
            }

        case UnOp(uop, a1) =>
            assert Serialize(a1) + [UnOpCode(uop)] + cds == Serialize(a1) + ([UnOpCode(uop)] + cds); 
        
            calc {
                DeserializeAux(Serialize(ae) + cds, es);
                == //by case
                    DeserializeAux(Serialize(UnOp(uop, a1)) + cds, es);
                == //by definition do serialize: Serialize do case UnOp ( op , a1 ) => Serialize ( a1 )+[ UnOpCode ( op )]
                    DeserializeAux(Serialize ( a1 )+[ UnOpCode ( uop )] + cds, es); 
                == { DeserializeInverseOfSerialize1(a1, [UnOpCode(uop)] + cds, es); }

                    DeserializeAux([UnOpCode(uop)] + cds, [ a1 ] + es);
                == 
                    DeserializeAux(([UnOpCode(uop)] + cds), [ a1 ] + es);
                == 
                    DeserializeAux(cds, DeserializeCode(UnOpCode(uop), [ a1 ] + es));
                ==
                    DeserializeAux(cds, [ UnOp(uop, a1) ] + es); 
                == //by case
                    DeserializeAux(cds, [ ae ] + es);
            }

        
        case BinOp(bop, a1, a2) =>
            assert Serialize(a2) + Serialize(a1) + [BinOpCode(bop)] + cds == Serialize(a2) + (Serialize(a1) + [BinOpCode(bop)] + cds);
            assert Serialize(a1) + [BinOpCode(bop)] + cds == Serialize(a1) + ([BinOpCode(bop)] + cds); 
            assert  [ a1 ] + ([ a2 ] + es) == [ a1, a2] + es;
            calc {
                DeserializeAux(Serialize(ae) + cds, es);
                ==
                    DeserializeAux(Serialize(BinOp(bop, a1, a2)) + cds, es);
                == 
                    DeserializeAux(Serialize(a2)+ Serialize(a1) + [ BinOpCode ( bop )] + cds, es); 
                ==
                    DeserializeAux(Serialize(a2)+ (Serialize(a1) + [ BinOpCode ( bop )] + cds), es); 
                == { DeserializeInverseOfSerialize1(a2, Serialize(a1) + [BinOpCode(bop)] + cds, es); }
                    DeserializeAux(Serialize(a1) + [BinOpCode(bop)] + cds, [ a2 ] + es);
                == 
                    DeserializeAux(Serialize(a1) + ([BinOpCode(bop)] + cds), [ a2 ] + es);
                == { DeserializeInverseOfSerialize1(a1, [ BinOpCode(bop) ] + cds, [ a2 ] + es); }
                    DeserializeAux([BinOpCode(bop)] + cds, [ a1, a2 ] + es);
                ==
                    DeserializeAux(cds, DeserializeCode(BinOpCode(bop), [a1, a2 ] + es));
                == 
                    DeserializeAux(cds, [ BinOp(bop,a1, a2)] + es); 
                == 
                    DeserializeAux(cds, [ ae ] + es);
            }
    }
}


lemma DeserializeInverseOfSerialize2(a : aexpr)
    ensures Deserialize(Serialize(a)) == [a]
{
    assert Serialize(a) + [] == Serialize(a); 

    calc {
        Deserialize(Serialize(a));
        == // by the definition of Deserialize 
            DeserializeAux(Serialize(a), []);
        ==  
            DeserializeAux(Serialize(a) + [], []);       
        ==  {DeserializeInverseOfSerialize1(a, [], []);} 
            DeserializeAux([], [a] + []);
        == 
            DeserializeAux([], [a]);
        ==  //by definition
            [a];
    }
}
//1.3 SerializeCodes and DeserializeCodes

function SerializeCodes(cds: seq<code>) : seq<nat> {
    if cds == [] 
        then []
    else 
        match cds[0] {
            case VarCode(s) => [0, |s|] + s + SerializeCodes(cds[1..])  
            case ValCode(i) => [1, i] + SerializeCodes(cds[1..])   
            case UnOpCode(uop) =>
                match uop {
                    case Neg => [ 2 ] + SerializeCodes(cds[1..]) 
                }
            case BinOpCode(bop) =>
                match bop {
                    case Plus => [ 3 ] + SerializeCodes(cds[1..])
                    case Minus => [ 4 ] + SerializeCodes(cds[1..])
                }
        }
}


function DeserializeCodes(nats: seq<nat>) : seq<code>
    decreases nats
{
    if nats == [] 
        then []
    else
        match nats[0] {
            case 0 =>
                if |nats| >= 2 then 
                    var len := nats[1];
                    if |nats| >= 2 + len then 
                        [VarCode(nats[2..2+len])] + DeserializeCodes(nats[2+len..])
                    else []
                else []

            case 1 =>
                if |nats| >= 2
                    then [ValCode(nats[1])] + DeserializeCodes(nats[2..])
                else []

            case 2 =>
                [UnOpCode(Neg)] + DeserializeCodes(nats[1..]) 

            case 3 =>
                [BinOpCode(Plus)] + DeserializeCodes(nats[1..]) 

            case 4 =>
                [BinOpCode(Minus)] + DeserializeCodes(nats[1..])

            case _ => [] 
        }
}


//1.4
lemma DeserializeInverseOfSerializeCodes(cs: seq<code>)
    ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
    // Indução sobre a sequência de códigos
    if |cs| == 0 {
        // Caso base: uma sequência vazia
        calc {
            DeserializeCodes(SerializeCodes([]));
            == // pela definição de SerializeCodes
            DeserializeCodes([]);
            == // pela definição de DeserializeCodes para sequência vazia
            [];
        }
    } else {
        // Caso indutivo: assumimos que o lema vale para cs[1..]
        match cs[0] {
            case VarCode(s) =>
                calc {
                    DeserializeCodes(SerializeCodes(cs));
                    == // pela definição de SerializeCodes para VarCode
                    DeserializeCodes(SerializeCodes([VarCode(s)] + cs[1..]));
                    ==
                    DeserializeCodes([0, |s|] + s + SerializeCodes(cs[1..]));
                    == // pela definição de DeserializeCodes para VarCode 
                    [VarCode(s)] + DeserializeCodes(SerializeCodes(cs[1..]));
                    == {DeserializeInverseOfSerializeCodes(cs[1..]);}
                    [VarCode(s)] + cs[1..]; 
                    == 
                    cs;
                }
            
            case ValCode(i) =>
                calc {
                    DeserializeCodes(SerializeCodes(cs));
                    == 
                    DeserializeCodes(SerializeCodes([ValCode(i)] + cs[1..]));
                    ==
                    DeserializeCodes([1, i] + SerializeCodes(cs[1..]));
                    == 
                    [ValCode(i)] + DeserializeCodes(SerializeCodes(cs[1..]));
                    == {DeserializeInverseOfSerializeCodes(cs[1..]);}
                    [ValCode(i)] + cs[1..];
                    == 
                    cs;
                }
           
            case UnOpCode(Neg) =>
                calc {
                    DeserializeCodes(SerializeCodes(cs));
                    == 
                    DeserializeCodes([2] + SerializeCodes(cs[1..]));
                    == 
                    [UnOpCode(Neg)] + DeserializeCodes(SerializeCodes(cs[1..]));
                    == {DeserializeInverseOfSerializeCodes(cs[1..]);}
                    [UnOpCode(Neg)] + cs[1..];
                    == 
                    cs;
                }
            case BinOpCode(Plus) =>
                calc {
                    DeserializeCodes(SerializeCodes(cs));
                    == 
                    DeserializeCodes([3] + SerializeCodes(cs[1..]));
                    == 
                    [BinOpCode(Plus)] + DeserializeCodes(SerializeCodes(cs[1..]));
                    == {DeserializeInverseOfSerializeCodes(cs[1..]);}
                    [BinOpCode(Plus)] + cs[1..];
                    == 
                    cs;
                }
            
            case BinOpCode(Minus) =>
                calc {
                    DeserializeCodes(SerializeCodes(cs));
                    == 
                    DeserializeCodes([4] + SerializeCodes(cs[1..]));
                    ==
                    [BinOpCode(Minus)] + DeserializeCodes(SerializeCodes(cs[1..]));
                    == {DeserializeInverseOfSerializeCodes(cs[1..]);}
                    [BinOpCode(Minus)] + cs[1..];
                    == 
                    cs;
                }
        }
    }
}

//1.5

function FullSerialize(a: aexpr) : seq<nat> {
    SerializeCodes(Serialize(a))
}

function FullDeserialize(nats: seq<nat>) : seq<aexpr> {
    Deserialize(DeserializeCodes(nats))
}


//1.6

lemma FullDeserializeInverseOfFullSerialize(a: aexpr)
    ensures FullDeserialize(FullSerialize(a)) == [a]
{
   
    calc {
        FullDeserialize(FullSerialize(a));
        == 
        FullDeserialize(SerializeCodes(Serialize(a)));
        == 
        Deserialize(DeserializeCodes(SerializeCodes(Serialize(a))));
        == 
        { DeserializeInverseOfSerializeCodes(Serialize(a)); }
        Deserialize(Serialize(a));
        == 
        { DeserializeInverseOfSerialize2(a); }
        [a]; 
    }
}





