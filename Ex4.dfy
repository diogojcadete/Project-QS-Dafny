include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem(v: nat) returns (b: bool)
    requires Valid()
    ensures b == (v in this.content)
    {
       if (list == null) {
           b := false;
       } else {
           b := list.mem(v); //function from class node
       }
    }


method add(v: nat) 
  requires Valid()
  modifies this
  ensures this.content == old(this.content) + {v}
  ensures this.footprint == old(this.footprint) + {list}
  ensures Valid()
  ensures fresh(this.footprint-old(footprint))
  
{
  var b: bool;
  if list == null {
    b := false; 
  } else {
    b := mem(v); 
  }

  if (!b) { 
    if list == null {
      list := new Ex3.Node(v);
    } else {
      list := list.add(v);
    }


    this.content := list.content;
    this.footprint := list.footprint;
  }
}


method union(s: Set) returns (r: Set)
  requires Valid() && s.Valid()
  ensures r.Valid()
  ensures r.content == this.content + s.content 
  ensures fresh(r)
  ensures fresh(r.footprint)
{
  r := new Set();


  var cur1 := this.list;
  while (cur1 != null) 
    invariant cur1!= null ==> cur1.Valid()
    invariant cur1!= null ==> r.content + cur1.content == this.content
    invariant cur1 == null ==> r.content == this.content 
    invariant r.Valid()
    invariant fresh(r)
    invariant fresh(r.footprint)
    decreases if(cur1!=null) then cur1.footprint else{}
  {
    r.add(cur1.data); 
    cur1 := cur1.next;
  }

  
  var cur2 := s.list;
  while (cur2 != null) 
    invariant cur2!= null ==> cur2.Valid()
    invariant cur2!= null ==> r.content + cur2.content == s.content + this.content
    invariant cur2 == null ==> r.content == this.content + s.content
    invariant r.Valid()
    invariant fresh(r)
    invariant fresh(r.footprint)
    decreases if(cur2!=null) then cur2.footprint else{}
  {
    var b := r.mem(cur2.data); 
    if (!b) {
      r.add(cur2.data); 
    }
    cur2 := cur2.next;
  }
}


method inter(s: Set) returns (r: Set)
  requires Valid() && s.Valid()
  ensures r.Valid()
  ensures forall k: nat :: (k in r.content <==> (k in this.content && k in s.content)) 
  ensures fresh(r)
  ensures fresh(r.footprint)
{
  r := new Set();

  var cur1 := this.list;
  ghost var seen_Aux_array: set<nat> := {}; 

 
  while (cur1 != null)
    invariant cur1!= null ==> cur1.Valid()
    invariant cur1 != null ==>  this.content == seen_Aux_array + cur1.content      
    invariant cur1 == null ==>  this.content == seen_Aux_array    
    invariant forall k :: (k in seen_Aux_array && k in s.content) ==> k in r.content
    invariant forall k :: k in r.content ==> (k in this.content && k in s.content)
    invariant r.Valid()
    invariant fresh(r)
    invariant fresh(r.footprint)
    decreases if(cur1 != null) then cur1.footprint else {}
  {
    var b:= s.mem(cur1.data);
    if (b) {
      r.add(cur1.data);  
    }
    seen_Aux_array := seen_Aux_array + {cur1.data};
    cur1 := cur1.next;
  }
}
}
}
