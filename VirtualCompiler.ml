open Core.Std

type direction = In | Out
type port = int
type sw_id = int	      
	    
type location = { switch : sw_id
		; port : port
		; direction : direction
		}

type header_val =
  | Switch
  | Port
  | IPProto
  | Src
  | Dst
  | VSwitch
  | VPort

let (<=) (hv : header_val) (v : int) : (header_val * int) =
  (hv, v)

type header = (header_val, int) Map.Poly.t	      
type pattern = header -> bool
type action = header -> header option

let mkPattern (key : header_val) : ('a -> pattern) =
  fun x -> fun h ->
  match Map.Poly.find h key with
  | None -> false
  | Some v -> v = x

let switch : int -> pattern = mkPattern Switch
let port : int -> pattern = mkPattern Port
let ipProto : int -> pattern = mkPattern IPProto
let src : int -> pattern = mkPattern Src
let dst : int -> pattern = mkPattern Dst
let (&) (p0: pattern) (p1: pattern) : pattern =
  fun h -> p0 h && p1 h

let mkAction (headers : (header_val * int) list) : action =
  let add (key, data) h = Map.Poly.add h key data in
  fun h -> Some (List.fold_right headers ~f:add ~init:h)

let drop = None		
		
type program = (pattern * action) list

(* topology : location to a set of out edges *) 		 
type topology = (location, location Set.Poly.t) Map.Poly.t							 
	     
type source =
  (* virtual program *)
  { program : program
  (* virtual topology *)
  ; topology : topology
  (* virtual ingress locations *)
  ; ingress : location Set.Poly.t
  (* virtual egress locations *)
  ; egress : location Set.Poly.t
  (* maps physical ports to virtual ports *)
  ; relation : (location, location) Map.Poly.t
  }

let location (s : sw_id) (p : port) (d : direction) =
  { switch = s
  ; port = p
  ; direction = d
  }

let inOut (s : sw_id) (p : port) : (location * location) = (location s p In, location s p Out)

(* 
         Virtual Topology

   <---> (va) <----> (vb) <--->
 *)
		  
let va : sw_id = 0
let (va0in, va0out) = inOut va 0
let (va1in, va1out) = inOut va 1

let vb : sw_id = 1
let (vb0in, vb0out) = inOut vb 0
let (vb1in, vb1out) = inOut vb 1

let vtopo : topology =
  Map.Poly.of_alist_exn [ (va0in, Set.Poly.of_list [va0out; va1out])
			; (va1in, Set.Poly.of_list [va0out; va1out])
			; (va0out, Set.Poly.of_list [])
			; (va1out, Set.Poly.of_list [vb0in])
			; (vb0in, Set.Poly.of_list [vb0out; vb1out])
			; (vb1in, Set.Poly.of_list [vb0out; vb1out])
			; (vb0out, Set.Poly.of_list [va1in])
			; (vb1out, Set.Poly.of_list [])
			]

let vingress: location Set.Poly.t = Set.Poly.of_list [va0in; vb1in]
let vegress: location Set.Poly.t = Set.Poly.of_list [va0out; vb1out]
			
(* Simple Forwarding on Virtual Topology *)
let simpleForwarding : program =
  let inOut = (port 0, mkAction [Port <= 1]) in
  let inOut' = (port 1, mkAction [Port <= 0]) in
  [inOut; inOut']
			
(* 
          Physical Topology

                (pb)
              /     \
          (pa)     (pc)
            \      /
              (pd)
 *)			

let pa : sw_id = 0
let (pa0in, pa0out) = inOut pa 0
let (pa1in, pa1out) = inOut pa 1
let (pa2in, pa2out) = inOut pa 2
			    
let pb : sw_id = 1
let (pb0in, pb0out) = inOut pb 0
let (pb1in, pb1out) = inOut pb 1
		   
let pc : sw_id = 2
let (pc0in, pc0out) = inOut pc 0
let (pc1in, pc1out) = inOut pc 1
let (pc2in, pc2out) = inOut pc 2

let pd : sw_id = 3
let (pd0in, pd0out) = inOut pd 0
let (pd1in, pd1out) = inOut pd 1

let ptopo : topology =
  Map.Poly.of_alist_exn []

let pingress = Set.Poly.of_list [pa0in, pc0in]
let pegress = Set.Poly.of_list [pa0out, pc0out]


let relation = Map.Poly.of_alist_exn [ (va0in, pa0in)
				     ; (va0out, pa0out)
				     ; (vb1in, pc0in)
				     ; (vb1out, pc0out) ]

let source : source = { program = simpleForwarding
		      ; topology = vtopo
		      ; ingress = vingress
		      ; egress = vegress
		      ; relation = relation
		      }
				     

(* Given a Set of Ingress locations in a physical, create a lifting program *)
let liftIn (ingress : location Set.Poly.t) (source : source) : program =
  let ls =  Set.Poly.to_list ingress in
  let build ploc pgm =
    let vloc = Map.Poly.find_exn source.relation ploc in
    let pattern = switch ploc.switch & port ploc.port in
    let action = mkAction [VPort <= vloc.port; VSwitch <= vloc.switch] in
    (pattern, action)::pgm
  in
  List.fold_right ls ~f:build ~init:[]

type node = { vloc : location
	    ; ploc : location
	    }
		  
type edge = { s : node
	    ; d : node
	    }

let isConsistent (n : node) (source : source) : bool =
  match Map.Poly.find source.relation n.vloc with
  | None -> false
  | Some loc -> loc = n.ploc
		  
let edges (node : node) (source : source) (ptopo : topology) : edge Set.Poly.t =
  let vneighbors = Map.Poly.find_exn source.topology node.vloc in
  let vmoves = 
    Set.Poly.map vneighbors ~f:(fun vn -> { s = node
					  ; d = { vloc = vn
						; ploc = node.ploc
						}
					  } )
  in
  let pneighbors = Map.Poly.find_exn ptopo node.ploc in
  let pmoves =
    Set.Poly.map pneighbors ~f:(fun pn -> { s = node
					  ; d = { vloc = node.vloc
						; ploc = pn
						}
					  } )
  in
  (*  let pmoves' = Set.Poly.filter pmoves ~f:(fun n -> isConsistent n.d source) *)
  (*  in *)
  let nomoves = if (isConsistent node source) then Set.Poly.singleton { s = node; d = node } else Set.Poly.empty
  in Set.Poly.union_list [ vmoves; pmoves; nomoves ]

type node_properties = { inEdges : node Set.Poly.t
		       ; outEdges : node Set.Poly.t
		       }
			 
type graph = { edges : edge Set.Poly.t
	     ; nodes : (node, node_properties) Map.Poly.t
	     }

let updateNodeIn m n0 n1 =
  let current = match Map.Poly.find m n0 with
    | None -> { inEdges = Set.Poly.empty; outEdges = Set.Poly.empty }
    | Some p -> p
  in
  let inEdges' = Set.Poly.add current.inEdges n1 in
  let update =
    { inEdges = inEdges'
    ; outEdges = current.outEdges
    }
  in Map.Poly.add m n0 update
		  
let updateNodeOut m n0 n1 =
  let current = match Map.Poly.find m n0 with
    | None -> { inEdges = Set.Poly.empty; outEdges = Set.Poly.empty }
    | Some p -> p
  in
  let outEdges' = Set.Poly.add current.outEdges n1 in
  let update =
    { inEdges = current.inEdges
    ; outEdges = outEdges'
    }
  in Map.Poly.add m n0 update
	       
let addEdge (e: edge) ( m : (node, node_properties) Map.Poly.t ) : (node, node_properties) Map.Poly.t =
  updateNodeIn (updateNodeOut m e.s e.d) e.d e.s
	       
let buildGraph (edges : edge Set.Poly.t) : graph =
  { edges = edges
  ; nodes = Set.Poly.fold_right edges ~f:addEdge ~init:Map.Poly.empty
  }

let rec searchAndMark (g: graph) (n : node) (marked : node Set.Poly.t) : node Set.Poly.t =
  let props = Map.Poly.find_exn g.nodes n in
  let marked' = Set.Poly.add marked n in
  let outEdges' = Set.Poly.filter props.outEdges ~f:(fun o -> not (Set.Poly.mem marked' o)) in
  Set.Poly.fold_right outEdges' ~f:(searchAndMark g) ~init:marked'  

let addEdges (reachable : node Set.Poly.t) (g : graph) (n : node) ( edges : edge Set.Poly.t) : edge Set.Poly.t =
  let neighbors = Map.Poly.find_exn g.nodes n in
  let inEdges = Set.Poly.filter neighbors.inEdges ~f:(fun n -> Set.Poly.mem reachable n) in
  let inEdges' = Set.Poly.map inEdges ~f:(fun src -> { s = src; d = n }) in
  let outEdges = Set.Poly.filter neighbors.outEdges ~f:(fun n -> Set.Poly.mem reachable n) in
  let outEdges' = Set.Poly.map outEdges ~f:(fun dst -> { s = n; d = dst }) in
  Set.Poly.union_list [edges; outEdges'; inEdges']    
		      
let removeUnreachable (g : graph) (source : source) : graph =
  let startNodes : node Set.Poly.t =
    Set.Poly.map source.ingress ~f:(fun vloc -> { vloc = vloc;
						  ploc = Map.Poly.find_exn source.relation vloc
						})
  in
  let reachable = Set.Poly.fold_right startNodes ~f:(searchAndMark g) ~init:Set.Poly.empty in
  let leftOverEdges = Set.Poly.fold_right reachable ~f:(addEdges reachable g) ~init:Set.Poly.empty in
  buildGraph leftOverEdges

let removeNode (n : node) (g : graph) : graph =
  let edges' = Set.Poly.filter g.edges ~f:(fun e -> not (e.s = n || e.d = n))
  in buildGraph edges'
	     
let rec removeFatal (g : graph) : graph =
  let noOut = Map.Poly.filter g.nodes ~f:(fun ~key ~data -> (Set.Poly.length data.outEdges) = 0) in
  if Map.Poly.length noOut = 0 then g
  else let g' = List.fold_right (Map.Poly.keys noOut) ~f:(removeNode) ~init:g
       in removeFatal g'
