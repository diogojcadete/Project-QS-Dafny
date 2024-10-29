include "Ex3.dfy"

module Ex5 {
  
  import Ex3 = Ex3

  class Set {
    var tbl : array<bool> // Array for constant time membership checking
    var list : Ex3.Node? // Linked list representation of the set

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, tbl, this.list, footprint
    {
      // Check if the footprint is consistent with the list and content
      if (this.list == null)
        then 
          this.footprint == {}
          && 
          this.content == {}
      else 
          this.footprint == list.footprint
          && 
          this.content == list.content
          &&
          forall v :: (v in this.content && 0 <= v < tbl.Length ==> tbl[v] == true)
          &&
          forall v :: (0 <= v < tbl.Length && tbl[v] == true ==> v in this.content)
          &&
          list.Valid()
    }

    constructor (size : nat) 
      requires size > 0
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      var tbl := new bool[size]; 
      for i := 0 to size - 1 {
        tbl[i] := false; 
      }
      list := null; 
      footprint := {}; 
      content := {}; 
    }

method mem (v : nat) returns (b : bool)
requires Valid()
ensures b == (v < tbl.Length && tbl[v]) 
{
  if (v < tbl.Length) { 
    b := tbl[v]; 
  } else {
    b := false;
  }
}


method add(v: nat) 
requires Valid()
ensures v < tbl.Length && !tbl[v] ==> this.content == old(this.content) + {v} 
ensures this.footprint == old(this.footprint) + {list}
ensures Valid()
ensures fresh(this.footprint-old(footprint))
modifies this, tbl
{
  var b: bool;
  if list == null {
    b := false; 
  } else {
    b := this.mem(v); 
  }
    if (!b) {
        
        if (v < tbl.Length) {
            tbl[v] := true;
        }

        if list == null {
        
            list := new Ex3.Node(v);
        } else {
            list := list.add(v); 
            
        }

        // Update ghost variables after successful addition
        this.content := list.content; // Update the content set
        this.footprint := list.footprint; // Update the footprint to match the new list
    }
  
}
method unionV1(s: Set) returns (r: Set)
  requires Valid() && s.Valid()
  ensures r.Valid()
  ensures r.content == this.content + s.content
  ensures forall i :: 0 <= i < r.tbl.Length && (i in this.content || i in s.content) ==> r.tbl[i] == true
  ensures fresh(r)
{
  
  r := new Set(this.tbl.Length + s.tbl.Length + 1); 

  
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
  r := new Set(this.tbl.Length + s.tbl.Length + 1);

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



