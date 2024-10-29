module Ex3 {

  class Node {

    var data : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.data }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.data } + this.next.content
          &&
          this.next.Valid()
    }

    constructor(v: nat) 
    ensures Valid()
    ensures this.data == v 
    ensures this.next == null
    {
        data := v;
        this.next := null;
        this.content := {v};
        this.footprint := {this};
    }


   method add(i:nat) returns (r: Node)
    requires Valid()
    ensures r.Valid() && r.content == {i} + this.content && r.footprint == {r} + this.footprint
    ensures fresh(r) 

    {
        r:= new Node(i);
        r.next := this;
        r.content := {i} + this.content;
        r.footprint := {r} + this.footprint;
    }

    method mem(i: nat) returns (b:bool)
    requires Valid()
    ensures b == (i in this.content) 
    {
        var cur:= this;
        b:=false; 
        ghost var set_aux := {}; 
        while(cur!=null)
        invariant cur!= null ==> cur.Valid()
        invariant cur!= null ==> this.content == set_aux +cur.content      
        invariant cur== null ==> this.content == set_aux
        invariant i !in set_aux
        decreases if(cur!= null) then cur.footprint else{}
        {
            if(cur.data == i){ 
                b:= true; return;
            }
            set_aux := set_aux + {cur.data};
            cur:=cur.next;

        }
    }
    method copy()returns(r:Node)
    requires this.Valid()
    ensures r.Valid() && this.content == r.content 
    ensures fresh(r.footprint) 
    decreases this.footprint
    {
        r:= new Node(this.data);
        if(this.next != null){
            var aux:= this.next.copy(); 
            r.next := aux;      
            r.content:= {r.data} + aux.content;
            r.footprint := {r} + aux.footprint;

        }
    }
  
  }

}
