/*
 * Nicebook - Operations
 */

open privacy

abstract sig Operation{}
abstract sig ContentOperations extends Operation{u:User, c:Content}
sig addComment extends ContentOperations{
	new : Comment // a new comment is added to a piece of content
}{
	// Preconditions
	new not in c
	// user can add comment iff he/she can view this content and has permission to comment
	c in viewable[u]
	u in getGroup[contentOwner[c],contentOwner[c].userContentCommentPL]
	// Postcondition
	new.commentBelongContent = c
	new.contentBelongUser = u
}

