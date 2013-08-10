:- use_module(library(chr)).

%%%%%%%%%%%%%%
% Data Types %
%%%%%%%%%%%%%%

:- chr_type chunk_def ---> nil; chunk(any, any, slot_list).
:- chr_type list(T) ---> []; [T | list(T)].
% a list of slot-value pairs
:- chr_type slot_list == list(pair(any,any)).
:- chr_type pair(T1,T2) ---> (T1,T2).

:- chr_type lchunk_defs == list(chunk_def).

%%%%%%%%%%%%%%%%%%%%
% Data Constraints %
%%%%%%%%%%%%%%%%%%%%

:- chr_constraint chunk(+,+).
% chunk(ChunkName, ChunkType)
% 

:- chr_constraint chunk_type(+).

:- chr_constraint chunk_type_has_slot(+,+).
% chunk_type_has_slot(ChunkTypeName, SlotName).

:- chr_constraint chunk_has_slot(+,+,+).
% chunk_has_slot(ChunkName, SlotName, Value)

:- chr_constraint alter_slots(+,+slot_list), alter_slot(+,+,+).  

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Procedural Constraints %
%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% public

:- chr_constraint add_chunk_type(+,+).
% add_chunk_type(+ChunkTypeName, +Slots)
% Adds a new chunk type with name ChunkTypeName to the system. The slots are defined in the list Slots.

:- chr_constraint add_chunk(+chunk_def).
% add_chunk(+Chunk)
% Adds a chunk defined by Chunk to the store.
% The argument Chunk must be of type chunk.

:- chr_constraint add_chunks(+lchunk_defs).
% add_chunks(+ListofChunks)
% Adds a chunk defined by Chunk to the store.
% The argument Chunk must be a list of chunk definitions.

:- chr_constraint remove_chunk(+).
% remove_chunk(ChunkName)
% removes the chunk with name ChunkName from the store.

:- chr_constraint return_chunk(+,-chunk_def).

%
% private

:- chr_constraint build_chunk_list(+chunk_def,-chunk_def).

:- chr_constraint do_add_chunk(+chunk_def).

%%%%%%%%%
% Rules %
%%%%%%%%%


add_chunk_type(CT, []) <=> chunk_type(CT).
add_chunk_type(CT, [S|Ss]) <=> chunk_type_has_slot(CT, S), add_chunk_type(CT, Ss).

% 
% Adding of multiple chunks at once
add_chunks([]) <=> true.
add_chunks([C|Cs]) <=> add_chunk(C), add_chunks(Cs).

% empty chunk will not be added
add_chunk(nil) <=> true.
 
% initialize all slots with nil. This leads to complete chunk definitions in store. Values that are not set stay nil.
add_chunk(chunk(Name,Type, _)), chunk_type_has_slot(Type,S) ==> 
  chunk_has_slot(Name,S,nil).

% chunk has been initialized with empty slots -> actually add chunk
add_chunk(chunk(Name,Type, Slots)) <=>
  do_add_chunk(chunk(Name,Type,Slots)).

% base case
do_add_chunk(chunk(Name, Type, [])) <=> chunk(Name, Type). 

% overwrite slots with empty values
chunk(V,_) \ do_add_chunk(chunk(Name, Type, [(S,V)|Rest])), chunk_has_slot(Name,S,nil)  <=> 
  chunk_has_slot(Name, S,V), 
  do_add_chunk(chunk(Name,Type,Rest)).

% overwrite slots with empty values  
do_add_chunk(chunk(Name, Type, [(S,V)|Rest])), chunk_has_slot(Name,S,nil)  <=>
  V == nil | % do not add chunk(nil,chunk)
  chunk_has_slot(Name, S,V), 
  do_add_chunk(chunk(Name,Type,Rest)).  

% overwrite slots with empty values  
do_add_chunk(chunk(Name, Type, [(S,V)|Rest])), chunk_has_slot(Name,S,nil)  <=> 
  V \== nil |
  chunk_has_slot(Name, S,V), 
  chunk(V,chunk), % no chunk for slot value found => add chunk of type chunk
  do_add_chunk(chunk(Name,Type,Rest)).
  
alter_slots(_,[]) <=> true.
alter_slots(Chunk,[(S,V)|SVs]) <=> 
  alter_slot(Chunk,S,V),
  alter_slots(Chunk,SVs).
  
alter_slot(Chunk,Slot,Value), chunk_has_slot(Chunk,Slot,_) <=>
  chunk_has_slot(Chunk,Slot,Value).
  
alter_slot(Chunk,Slot,Value) <=>
  false. % since every chunk must be described completely, Slot cannot be a slot of the type of Chunk
  %chunk_has_slot(Chunk,Slot,Value).
  
remove_chunk(Name) \ chunk(Name, _) <=> true.
remove_chunk(Name) \ chunk_has_slot(Name, _, _) <=> true.
remove_chunk(_) <=> true.  
  
chunk(ChunkName, ChunkType) \ return_chunk(ChunkName,Res) <=> var(Res) | build_chunk_list(chunk(ChunkName, ChunkType, []),Res).

chunk_has_slot(ChunkName, S, V) \ build_chunk_list(chunk(ChunkName, ChunkType, L), Res) <=> \+member((S,V),L) | build_chunk_list(chunk(ChunkName, ChunkType, [(S,V)|L]),Res).
build_chunk_list(X,Res) <=> Res=X.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%% Buffer System %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- chr_constraint add_buffer(+).
% add_buffer(+BufferName)
% adds a new buffer with name BufferName for module ModuleName. 
% Buffers must have distinct names!
% A module can have multiple buffers.

:- chr_constraint buffer(+,+).
% buffer(Name, ChunkName)

:- chr_constraint buffer_state/2, set_buffer_state/2.

:- chr_constraint set_buffer(+,+chunk_def).
:- chr_constraint write_to_dm(+).
:- chr_constraint buffer_change/2, buffer_clear/1.

% create empty buffer
add_buffer(BufName) <=> 
  buffer(BufName, nil),
  buffer_state(BufName,free). 

set_buffer(BufName, nil), buffer(BufName, _)  <=> 
  buffer(BufName, nil).
  
set_buffer(BufName, chunk(ChunkName, _, _)), buffer(BufName, _) <=>
  buffer(BufName, ChunkName).
  
set_buffer_state(BufName, State), buffer_state(BufName, _) <=> buffer_state(BufName, State).

%Handle buffer modification
buffer(BufName, _) \ buffer_change(BufName, nil) <=>
  set_buffer(BufName,nil).

buffer(BufName, nil) \ buffer_change(BufName, C) <=>
  add_chunk(C),
  set_buffer(BufName,C).

buffer(BufName, OldChunk) \ buffer_change(BufName, chunk(_,_,SVs)) <=>
  alter_slots(OldChunk,SVs).

alter_slots(_,[]) <=> true.
alter_slots(Chunk,[(S,V)|SVs]) <=> 
  alter_slot(Chunk,S,V),
  alter_slots(Chunk,SVs). 
  
% Handle buffer clearing  
buffer_clear(BufName), buffer(BufName, Chunk) <=> 
  %write_to_dm(Chunk), % not implemented yet
  remove_chunk(Chunk), 
  buffer(BufName, nil).
  