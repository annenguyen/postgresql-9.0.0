/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2010, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHashjoin.c,v 1.103 2010/01/02 16:57:41 momjian Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "utils/memutils.h"


/* Returns true for JOIN_LEFT and JOIN_ANTI jointypes */
#define HASHJOIN_IS_OUTER(hjstate)	((hjstate)->hj_NullInnerTupleSlot != NULL)

static TupleTableSlot *ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot);
static int	ExecHashJoinNewBatch(HashJoinState *hjstate);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
	// CSI3130 adding corresponding inner varibles for each of the outer variables
	EState	   *estate;
	
	// CSI3130 renamed and added one
	HashState  *hashNodeOuter;
	HashState  *hashNodeInner;
	List	   *joinqual;
	List	   *otherqual;
	TupleTableSlot *inntuple;
	TupleTableSlot *outtuple; // CSI3130 added
	ExprContext *econtext;
	ExprDoneCond isDone;

	// CSI3130 renamed and added one
	HashJoinTable hashtableInner;
	HashJoinTable hashtableOuter;
	HashJoinTuple curtuple;

	// CSI3130 renamed and added one
	TupleTableSlot *outerTupleSlot;
	TupleTableSlot *innerTupleSlot;
	uint32		hashvalue;
	int			batchno;

	/*
	 * get information from HashJoin node
	 */
	estate = node->js.ps.state;
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	// CSI 3130, correcting variable names, added inner relation info
	hashNodeInner = (HashState *) innerPlanState(node);
	hasNodeOuter = (HashState *) outerPlanState(node);

	/*
	 * get information from HashJoin state
	 */
	// CSI 3130, correcting variable names, added inner relation info
	hashtableOuter = node->hj_HashTableOuter;
	hashtableInner = node->hj_HashTableInner;
	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */

	// CSI 3130, don't need this for our implementation
	// if (node->js.ps.ps_TupFromTlist)
	// {
	// 	TupleTableSlot *result;

	// 	result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
	// 	if (isDone == ExprMultipleResult)
	// 		return result;
	// 	/* Done with that source tuple... */
	// 	node->js.ps.ps_TupFromTlist = false;
	// }

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * if this is the first call, build the hash table for inner relation
	 */
	// CSI3130 if both tables are null
	if (hashtableInner == NULL && hashtableOuter == NULL)
	{
		/*
		 * If the outer relation is completely empty, we can quit without
		 * building the hash table.  However, for an inner join it is only a
		 * win to check this when the outer relation's startup cost is less
		 * than the projected cost of building the hash table.	Otherwise it's
		 * best to build the hash table first and see if the inner relation is
		 * empty.  (When it's an outer join, we should always make this check,
		 * since we aren't going to be able to skip the join on the strength
		 * of an empty inner relation anyway.)
		 *
		 * If we are rescanning the join, we make use of information gained on
		 * the previous scan: don't bother to try the prefetch if the previous
		 * scan found the outer relation nonempty.	This is not 100% reliable
		 * since with new parameters the outer relation might yield different
		 * results, but it's a good heuristic.
		 *
		 * The only way to make the check is to try to fetch a tuple from the
		 * outer plan node.  If we succeed, we have to stash it away for later
		 * consumption by ExecHashJoinOuterGetTuple.
		 */
		
		// CSI3130 cost caluclating code removed, not required for our implementation

		/*
		 * create the hash table
		 */
		hashtableInner = ExecHashTableCreate((Hash *) hashNodeInner->ps.plan,
										node->hj_HashOperators);
		node->hj_HashTableInner = hashtableInner;
		
		// CSI3130 repeat above for outer relation
		hashtableOuter = ExecHashTableCreate((Hash *) hashNodeOuter->ps.plan,
										node->hj_HashOperators);
		node->hj_HashTableOuter = hashtableOuter;


		/*
		 * execute the Hash node, to build the hash table
		 */
		hashNodeInner->hashtable = hashtableInner;
		// CSI3130 repeat above for outer
		hashNodeOuter->hashtable = hashtableOuter;
		// (void) MultiExecProcNode((PlanState *) hashNode); CSI3130 -- not using this

		// CSI3130 code to deal with batches removed
	}

	/*
	 * run the hash join process
	 */
	// CSI3130 symmetric hash join implementation
	for (;;)
	{
		/*
		 * If there are still tuples in inner or outer
		 */
		
		if (node->hj_OuterNotEmpty || node->hj_InnerNotEmpty) {

			// if the inner is empty, then we need tuple from outer
			if(!node->hj_InnerNotEmpty){
				node->hj_NeedNewOuter = true;
				node->hj_NeedNewInner = false; 
			}

			// if the outer is empty, then we need tuple from inner
			if(!node->hj_OuterNotEmpty){
				node->hj_NeedNewOuter = false;
				node->hj_NeedNewInner = true; 
			}

			// hashing with inner tuples
			if (node->hj_InnerNotEmpty && node->hj_NeedNewInner) {

				// get the next inner tuple
				innerTupleSlot = ExecHashJoinInnerGetTuple(hashNodeInner,
													   node,
													   &hashvalue);
				
				// make sure tuple isn't null
				if(!TupIsNull(innerTupleSlot)){

					// adding this inner tuple, so reset need for inner tuple
					node->hj_NeedNewInner = false;
					econtext->ecxt_innertuple = innerTupleSlot;

					// get the hash of the inner tuple to the outer tables hash table
					// apply outer hash function to inner tuple
					hashvalue = ExecHashGetHashValue(hashtableOuter, econtext, node->hj_InnerHashKeys);
					// add the hashed value to the outer hash table
					// set the joinstate's planstate's resultTupleSlot
					node->js.ps.ps_ResultTupleSlot = innerTupleSlot;
					// update econtext accordingly
					econtext->ecxt_innertuple = innerTupleSlot;

					// check for a match (tuple from inner and outer where join condition is true)
					node->hj_CurHashValueInner = hashvalue;
					// found the bucket
					ExecHashGetBucketAndBatch(hashtableOuter, hashvalue,
									  &node->hj_CurBucketNoOuter, &batchno);
				
					node->hj_CurTupleOuter = NULL;

				} else {
					// if here then inner must be empty
					node->hj_InnerNotEmpty = false;
				}
			}
		}

		// now we repeat the process for the outer tuples

		if(node->hj_OuterNotEmpty && node->hj_NeedNewOuter) {

			// get the next outer tuple
			outerTupleSlot = ExecHashJoinOuterGetTuple(hashNodeOuter,
												   node,
												   &hashvalue);
			
			// make sure tuple isn't null
			if(!TupIsNull(outerTupleSlot)){

				// adding this outer tuple, so reset need for outer tuple
				node->hj_NeedNewOuter = false;
				econtext->ecxt_outertuple = outerTupleSlot;

				// get the hash of the outer tuple to the inner tables hash table
				// apply inner hash table's hash function to outer tuple 
				hashvalue = ExecHashGetHashValue(hashtableInner, econtext, node->hj_OuterHashKeys);
				// add the hashed value to the inner hash table
				// set the joinstate's planstate's resultTupleSlot
				node->js.ps.ps_ResultTupleSlot = outerTupleSlot;
				// update econtext accordingly
				econtext->ecxt_outertuple = outerTupleSlot;


				// check for a match (tuple from inner and outer where join condition is true)
				node->hj_CurHashValueOuter = hashvalue;
				ExecHashGetBucketAndBatch(hashtableInner, hashvalue,
								  &node->hj_CurBucketNoInner, &batchno);
			
				node->hj_CurTupleInner = NULL;

			} else {
				// if here then inner must be empty
				node->hj_OuterNotEmpty = false;
			}
		}

		// are there any more tuples? 
		if(!node->hj_InnerNotEmpty && !node->hj_OuterNotEmpty) {
			/* end of join */
			return NULL;
		}

		/*
		 * OK, scan the selected hash bucket for matches
		 */

		// first check on inner matches
		if(!TupIsNull(node->js.ps.ps_ResultTupleSlot) && node->hj_NeedNewInner){
			
			for(;;) { // loop until there are no more matched tuples
				curtuple = ExecScanHashBucket(node, econtext);
				if (curtuple == NULL) {
					// no more matches found, update variable and kill loop
					node->hj_NeedNewInner = false;
					break;
				}
				/*
		 		* we've got a match, but still need to test non-hashed quals
				 */
				outtuple = ExecStoreMinimalTuple(HJTUPLE_MINTUPLE(curtuple),
												 node->hj_HashTupleSlotOuter,
												 false);	/* don't pfree */
				econtext->ecxt_outertuple = outtuple;

				/* reset temp memory each time to avoid leaks from qual expr */
				ResetExprContext(econtext);

				if (joinqual == NIL || ExecQual(joinqual, econtext, false)){
					
					if (otherqual == NIL || ExecQual(otherqual, econtext, false)){
						TupleTableSlot *result;

						result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

						if (isDone != ExprEndResult)
						{
							// the resulting join tuple
							node->js.ps.ps_TupFromTlist =
								(isDone == ExprMultipleResult);
							return result;
						}
					}	
				}
			}
			// done with the inner matches
			node->hj_NeedNewInner = false;
			node->js.ps.ps_InnerTupleSlot=NULL;
			
		}

		// now we repeat for outer tuples

		if(!TupIsNull(node->js.ps.ps_ResultTupleSlot) && node->hj_NeedNewOuter){
			
			for(;;) { // loop until there are no more matched tuples
				curtuple = ExecScanHashBucket(node, econtext);
				if (curtuple == NULL) {
					// no more matches found, update variable and kill loop
					node->hj_NeedNewOuter = false;
					break;
				}
				/*
		 		* we've got a match, but still need to test non-hashed quals
				 */
				inntuple = ExecStoreMinimalTuple(HJTUPLE_MINTUPLE(curtuple),
												 node->hj_HashTupleSlotInner,
												 false);	/* don't pfree */
				econtext->ecxt_innertuple = inntuple;

				/* reset temp memory each time to avoid leaks from qual expr */
				ResetExprContext(econtext);

				if (joinqual == NIL || ExecQual(joinqual, econtext, false)){
					
					if (otherqual == NIL || ExecQual(otherqual, econtext, false)){
						TupleTableSlot *result;

						result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

						if (isDone != ExprEndResult)
						{
							// the resulting join tuple
							node->js.ps.ps_TupFromTlist =
								(isDone == ExprMultipleResult);
							return result;
						}
					}	
				}
			}
			// done with the outer matches
			node->hj_NeedNewOuter = false;
			node->js.ps.ps_OuterTupleSlot=NULL;
			
		}
	}


}

/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate, int eflags)
{
	HashJoinState *hjstate;
	Plan	   *outerNode;
	Hash	   *hashNode;
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;

	/* check for unsupported flags */
	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	/*
	 * create state structure
	 */
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);

	/*
	 * initialize child expressions
	 */
	hjstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) hjstate);
	hjstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) hjstate);
	hjstate->js.jointype = node->join.jointype;
	hjstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) hjstate);
	hjstate->hashclauses = (List *)
		ExecInitExpr((Expr *) node->hashclauses,
					 (PlanState *) hjstate);

	/*
	 * initialize child nodes
	 *
	 * Note: we could suppress the REWIND flag for the inner input, which
	 * would amount to betting that the hash will be a single batch.  Not
	 * clear if this would be a win or not.
	 */
	outerNode = outerPlan(node);
	hashNode = (Hash *) innerPlan(node);

	outerPlanState(hjstate) = ExecInitNode(outerNode, estate, eflags);
	innerPlanState(hjstate) = ExecInitNode((Plan *) hashNode, estate, eflags);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);

	/* note: HASHJOIN_IS_OUTER macro depends on this initialization */
	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_SEMI:
			break;
		case JOIN_LEFT:
		case JOIN_ANTI:
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}

	/*
	 * now for some voodoo.  our temporary tuple slot is actually the result
	 * tuple slot of the Hash node (which is our inner plan).  we do this
	 * because Hash nodes don't return tuples via ExecProcNode() -- instead
	 * the hash join node uses ExecScanHashBucket() to get at the contents of
	 * the hash table.	-cim 6/9/91
	 */
	{
		HashState  *hashstate = (HashState *) innerPlanState(hjstate);
		TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;

		hjstate->hj_HashTupleSlot = slot;
	}

	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	ExecAssignProjectionInfo(&hjstate->js.ps, NULL);

	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot,
						  ExecGetResultType(outerPlanState(hjstate)));

	/*
	 * initialize hash-specific info
	 */
	hjstate->hj_HashTable = NULL;
	hjstate->hj_FirstOuterTupleSlot = NULL;

	hjstate->hj_CurHashValue = 0;
	hjstate->hj_CurBucketNo = 0;
	hjstate->hj_CurSkewBucketNo = INVALID_SKEW_BUCKET_NO;
	hjstate->hj_CurTuple = NULL;

	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;

		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = rclauses;

	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_NeedNewOuter = true;
	hjstate->hj_MatchedOuter = false;
	hjstate->hj_OuterNotEmpty = false;

	return hjstate;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash table
	 */
	if (node->hj_HashTable)
	{
		ExecHashTableDestroy(node->hj_HashTable);
		node->hj_HashTable = NULL;
	}

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_HashTupleSlot);

	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * ExecHashJoinOuterGetTuple
 *
 *		get the next outer tuple for hashjoin: either by
 *		executing a plan node in the first pass, or from
 *		the temp files for the hashjoin batches.
 *
 * Returns a null slot if no more outer tuples.  On success, the tuple's
 * hash value is stored at *hashvalue --- this is either originally computed,
 * or re-read from the temp file.
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue)
{
	HashJoinTable hashtable = hjstate->hj_HashTable;
	int			curbatch = hashtable->curbatch;
	TupleTableSlot *slot;

	if (curbatch == 0)			/* if it is the first pass */
	{
		/*
		 * Check to see if first outer tuple was already fetched by
		 * ExecHashJoin() and not used yet.
		 */
		slot = hjstate->hj_FirstOuterTupleSlot;
		if (!TupIsNull(slot))
			hjstate->hj_FirstOuterTupleSlot = NULL;
		else
			slot = ExecProcNode(outerNode);

		while (!TupIsNull(slot))
		{
			/*
			 * We have to compute the tuple's hash value.
			 */
			ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

			econtext->ecxt_outertuple = slot;
			if (ExecHashGetHashValue(hashtable, econtext,
									 hjstate->hj_OuterHashKeys,
									 true,		/* outer tuple */
									 HASHJOIN_IS_OUTER(hjstate),
									 hashvalue))
			{
				/* remember outer relation is not empty for possible rescan */
				hjstate->hj_OuterNotEmpty = true;

				return slot;
			}

			/*
			 * That tuple couldn't match because of a NULL, so discard it and
			 * continue with the next one.
			 */
			slot = ExecProcNode(outerNode);
		}

		/*
		 * We have just reached the end of the first pass. Try to switch to a
		 * saved batch.
		 */
		curbatch = ExecHashJoinNewBatch(hjstate);
	}

	/*
	 * Try to read from a temp file. Loop allows us to advance to new batches
	 * as needed.  NOTE: nbatch could increase inside ExecHashJoinNewBatch, so
	 * don't try to optimize this loop.
	 */
	while (curbatch < hashtable->nbatch)
	{
		slot = ExecHashJoinGetSavedTuple(hjstate,
										 hashtable->outerBatchFile[curbatch],
										 hashvalue,
										 hjstate->hj_OuterTupleSlot);
		if (!TupIsNull(slot))
			return slot;
		curbatch = ExecHashJoinNewBatch(hjstate);
	}

	/* Out of batches... */
	return NULL;
}

/*
 * ExecHashJoinNewBatch
 *		switch to a new hashjoin batch
 *
 * Returns the number of the new batch (1..nbatch-1), or nbatch if no more.
 * We will never return a batch number that has an empty outer batch file.
 */
static int
ExecHashJoinNewBatch(HashJoinState *hjstate)
{
	HashJoinTable hashtable = hjstate->hj_HashTable;
	int			nbatch;
	int			curbatch;
	BufFile    *innerFile;
	TupleTableSlot *slot;
	uint32		hashvalue;

start_over:
	nbatch = hashtable->nbatch;
	curbatch = hashtable->curbatch;

	if (curbatch > 0)
	{
		/*
		 * We no longer need the previous outer batch file; close it right
		 * away to free disk space.
		 */
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
	}
	else	/* we just finished the first batch */
	{
		/*
		 * Reset some of the skew optimization state variables, since we no
		 * longer need to consider skew tuples after the first batch. The
		 * memory context reset we are about to do will release the skew
		 * hashtable itself.
		 */
		hashtable->skewEnabled = false;
		hashtable->skewBucket = NULL;
		hashtable->skewBucketNums = NULL;
		hashtable->spaceUsedSkew = 0;
	}

	/*
	 * We can always skip over any batches that are completely empty on both
	 * sides.  We can sometimes skip over batches that are empty on only one
	 * side, but there are exceptions:
	 *
	 * 1. In an outer join, we have to process outer batches even if the inner
	 * batch is empty.
	 *
	 * 2. If we have increased nbatch since the initial estimate, we have to
	 * scan inner batches since they might contain tuples that need to be
	 * reassigned to later inner batches.
	 *
	 * 3. Similarly, if we have increased nbatch since starting the outer
	 * scan, we have to rescan outer batches in case they contain tuples that
	 * need to be reassigned.
	 */
	curbatch++;
	while (curbatch < nbatch &&
		   (hashtable->outerBatchFile[curbatch] == NULL ||
			hashtable->innerBatchFile[curbatch] == NULL))
	{
		if (hashtable->outerBatchFile[curbatch] &&
			HASHJOIN_IS_OUTER(hjstate))
			break;				/* must process due to rule 1 */
		if (hashtable->innerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_original)
			break;				/* must process due to rule 2 */
		if (hashtable->outerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_outstart)
			break;				/* must process due to rule 3 */
		/* We can ignore this batch. */
		/* Release associated temp files right away. */
		if (hashtable->innerBatchFile[curbatch])
			BufFileClose(hashtable->innerBatchFile[curbatch]);
		hashtable->innerBatchFile[curbatch] = NULL;
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
		curbatch++;
	}

	if (curbatch >= nbatch)
		return curbatch;		/* no more batches */

	hashtable->curbatch = curbatch;

	/*
	 * Reload the hash table with the new inner batch (which could be empty)
	 */
	ExecHashTableReset(hashtable);

	innerFile = hashtable->innerBatchFile[curbatch];

	if (innerFile != NULL)
	{
		if (BufFileSeek(innerFile, 0, 0L, SEEK_SET))
			ereport(ERROR,
					(errcode_for_file_access(),
				   errmsg("could not rewind hash-join temporary file: %m")));

		while ((slot = ExecHashJoinGetSavedTuple(hjstate,
												 innerFile,
												 &hashvalue,
												 hjstate->hj_HashTupleSlot)))
		{
			/*
			 * NOTE: some tuples may be sent to future batches.  Also, it is
			 * possible for hashtable->nbatch to be increased here!
			 */
			ExecHashTableInsert(hashtable, slot, hashvalue);
		}

		/*
		 * after we build the hash table, the inner batch file is no longer
		 * needed
		 */
		BufFileClose(innerFile);
		hashtable->innerBatchFile[curbatch] = NULL;
	}

	/*
	 * If there's no outer batch file, advance to next batch.
	 */
	if (hashtable->outerBatchFile[curbatch] == NULL)
		goto start_over;

	/*
	 * Rewind outer batch file, so that we can start reading it.
	 */
	if (BufFileSeek(hashtable->outerBatchFile[curbatch], 0, 0L, SEEK_SET))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not rewind hash-join temporary file: %m")));

	return curbatch;
}

/*
 * ExecHashJoinSaveTuple
 *		save a tuple to a batch file.
 *
 * The data recorded in the file for each tuple is its hash value,
 * then the tuple in MinimalTuple format.
 *
 * Note: it is important always to call this in the regular executor
 * context, not in a shorter-lived context; else the temp file buffers
 * will get messed up.
 */
void
ExecHashJoinSaveTuple(MinimalTuple tuple, uint32 hashvalue,
					  BufFile **fileptr)
{
	BufFile    *file = *fileptr;
	size_t		written;

	if (file == NULL)
	{
		/* First write to this batch file, so open it. */
		file = BufFileCreateTemp(false);
		*fileptr = file;
	}

	written = BufFileWrite(file, (void *) &hashvalue, sizeof(uint32));
	if (written != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) tuple, tuple->t_len);
	if (written != tuple->t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
}

/*
 * ExecHashJoinGetSavedTuple
 *		read the next tuple from a batch file.	Return NULL if no more.
 *
 * On success, *hashvalue is set to the tuple's hash value, and the tuple
 * itself is stored in the given slot.
 */
static TupleTableSlot *
ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot)
{
	uint32		header[2];
	size_t		nread;
	MinimalTuple tuple;

	/*
	 * Since both the hash value and the MinimalTuple length word are uint32,
	 * we can read them both in one BufFileRead() call without any type
	 * cheating.
	 */
	nread = BufFileRead(file, (void *) header, sizeof(header));
	if (nread == 0)				/* end of file */
	{
		ExecClearTuple(tupleSlot);
		return NULL;
	}
	if (nread != sizeof(header))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	*hashvalue = header[0];
	tuple = (MinimalTuple) palloc(header[1]);
	tuple->t_len = header[1];
	nread = BufFileRead(file,
						(void *) ((char *) tuple + sizeof(uint32)),
						header[1] - sizeof(uint32));
	if (nread != header[1] - sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	return ExecStoreMinimalTuple(tuple, tupleSlot, true);
}


void
ExecReScanHashJoin(HashJoinState *node, ExprContext *exprCtxt)
{
	/*
	 * In a multi-batch join, we currently have to do rescans the hard way,
	 * primarily because batch temp files may have already been released. But
	 * if it's a single-batch join, and there is no parameter change for the
	 * inner subnode, then we can just re-use the existing hash table without
	 * rebuilding it.
	 */
	if (node->hj_HashTable != NULL)
	{
		if (node->hj_HashTable->nbatch == 1 &&
			((PlanState *) node)->righttree->chgParam == NULL)
		{
			/*
			 * okay to reuse the hash table; needn't rescan inner, either.
			 *
			 * What we do need to do is reset our state about the emptiness of
			 * the outer relation, so that the new scan of the outer will
			 * update it correctly if it turns out to be empty this time.
			 * (There's no harm in clearing it now because ExecHashJoin won't
			 * need the info.  In the other cases, where the hash table
			 * doesn't exist or we are destroying it, we leave this state
			 * alone because ExecHashJoin will need it the first time
			 * through.)
			 */
			node->hj_OuterNotEmpty = false;
		}
		else
		{
			/* must destroy and rebuild hash table */
			ExecHashTableDestroy(node->hj_HashTable);
			node->hj_HashTable = NULL;

			/*
			 * if chgParam of subnode is not null then plan will be re-scanned
			 * by first ExecProcNode.
			 */
			if (((PlanState *) node)->righttree->chgParam == NULL)
				ExecReScan(((PlanState *) node)->righttree, exprCtxt);
		}
	}

	/* Always reset intra-tuple state */
	node->hj_CurHashValue = 0;
	node->hj_CurBucketNo = 0;
	node->hj_CurSkewBucketNo = INVALID_SKEW_BUCKET_NO;
	node->hj_CurTuple = NULL;

	node->js.ps.ps_TupFromTlist = false;
	node->hj_NeedNewOuter = true;
	node->hj_MatchedOuter = false;
	node->hj_FirstOuterTupleSlot = NULL;

	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (((PlanState *) node)->lefttree->chgParam == NULL)
		ExecReScan(((PlanState *) node)->lefttree, exprCtxt);
}