/*-------------------------------------------------------------------------------
Model of the Byzantine Generals Problem  

Created by:
John Phillips in November 2023

Edited by:
John Phillips in October 2024

Purpose:


Description: 

   
Assumptions:
1. The Commander is loyal. 
2. All messages sent are received. 
3. All messages cannot be changed in transit. 

Instructions:

Trace Count: 128 traces at Scope 1, 7 Generals, 1-7 Traitor
Elapsed time: 70.58 sec

TODOs: 
1. Implement tie breaker. I think this is present but need to confirm. 
2. Figure out how to find and remove mirror outcomes to speed up trace generation. 
3. Explore code for ways to speed up trace generation. 
-------------------------------------------------------------------------------*/ 

SCHEMA Byzantine_Generals_Problem

/* Placeholder variables to hold trace information. */
ATTRIBUTES { number a, b, c, d, e, f; };

ATTRIBUTES { number count, Lieutenants, Lieutenant_ID, Majority, node, Order, Orders, Traitor, Traitors; };

/* 1 = Attack
   0 = Retreat */
Orders := 1;

Lieutenants := 3; 
Traitors := 1;

Majority := Lieutenants / 2 + 0.5;

/* Used to track trace versions over time. */
SAY ( "Version 2024-10-17" );

/* Mark each trace with the trace number. */
SAY ( "Trace " trace_id );

ROOT Commander: 
	( Order_Attack | Order_Retreat )
	{+<3..3> Lieutenant +}

BUILD {
	
	Lieutenant_ID := 1;

	COORDINATE  $a: Lieutenant
		DO 
			$a.Lieutenant_ID := Lieutenant_ID; 
			Lieutenant_ID +:= 1; 
		OD;   
}
;

	Lieutenant:
		( 
        	( Attack_Ordered | Retreat_Ordered )
            Exchange_Messengers
        ( _Attack | _Retreat )
		)		
	;
	

COORDINATE	$a:	Commander
	DO
		IF Orders == 1 THEN ENSURE #Order_Attack == 1;
		ELSE ENSURE #Order_Retreat == 1; FI;
	OD;

/* Set the Order and find the Traitor(s) based on the Orders. */
count := 0;

COORDINATE	$a: Lieutenant
	DO COORDINATE $b: ( Attack_Ordered | Retreat_Ordered ) FROM $a
		DO IF $b IS Attack_Ordered THEN 
			$a.Order := 1; 
			IF Orders == 0 THEN
				$a.Traitor := 1; count +:= 1;
				ADD SAY("Traitor") PRECEDES $a;
			FI; 
		   FI;
		   
		   IF $b IS Retreat_Ordered THEN
		   	$a.Order := 0;
			IF Orders == 1 THEN
				$a.Traitor := 1; count +:= 1;
				ADD SAY("Traitor") PRECEDES $a;
			FI; 		   	
		 FI; OD;
	OD;

/* Set the number of Traitors. */
/*IF count != Traitors THEN REJECT; FI;*/

/* Set the maximum number of Traitors. */
/*IF count > Traitors THEN REJECT; FI;*/

count := 0;
node := 0; 
GRAPH messages { };

WITHIN messages {
	COORDINATE  $a: Lieutenant		
		DO COORDINATE $b: Lieutenant
		   	DO 		
    				/* What they said happened. */
    				Node$y: NEW ( node );
    				Node$y.a := ( $a.Lieutenant_ID );
				Node$y.b := ( $b.Lieutenant_ID );
    				IF $a.Traitor == 1 THEN
 					IF Orders == 1 THEN Node$y.c := 0; FI;
 					IF Orders == 0 THEN Node$y.c := 1; FI;
	
    				ELSE
    					Node$y.c := ( $b.Order );    							
    				FI;	
    				/* Keep track of the number of "Attack" orders. */
    				count +:= Node$y.c;										  										
    			OD;	
    			/*ADD SAY(count "|" Majority) PRECEDES $a;*/
    			count := 0;	
    			node +:= 1;	
		OD;  
}
;

count := 0;

COORDINATE	$a: Lieutenant
	DO count +:= $a.Order; OD;

/* In the event of a tie, the default is "Retreat".*/
IF ( count >= Majority ) THEN 
	IF #_Retreat > 0 THEN 
	CLEAR messages;
	REJECT; 
	FI;
FI;

IF ( count < Majority ) THEN  
	IF #_Attack > 0 THEN 
	CLEAR messages;
	REJECT; 
	FI; 
FI;
/*
COORDINATE $a: Lieutenant
	DO COORDINATE $b: ( _Attack | _Retreat ) FROM $a
		DO COORDINATE $c: Lieutenant
			DO COORDINATE $d: ( _Attack | _Retreat ) FROM $c
				DO
					SHARE $b $d;
				OD;
			OD;
		OD;
	OD;
*/		

/* Lieutenant G received a message from Lieutenant M with order O. */
TABLE message_table {
	TITLE ("Trace " trace_id " Message Table");
	TABS 	number Lieutenant,
			number was_told_by_Lieutenant,
    			number that_the_order_was;
}
;

WITHIN messages {
    FOR Node$n
    	DO   		
		message_table <|
    			Lieutenant:					Node$n.a,
			was_told_by_Lieutenant: 		Node$n.b,
    			that_the_order_was:			Node$n.c;
    	OD;

}
;

SHOW message_table;

CLEAR messages;
CLEAR message_table;