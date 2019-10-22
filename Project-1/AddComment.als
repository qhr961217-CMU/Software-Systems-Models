/*
 * Nicebook - Operations
 */

open basic
open privacy

abstract sig ContentOperations{u:User, c:Content}
sig addComment extends ContentOperations{
	new : Comment // a new comment is added to a piece of content
}{
	// Preconditions
	c in viewable[u]
	u in getGroup[contentOwner[c],contentOwner[c].userContentCommentPL]
	// Postcondition
	new.commentBelongContent = c
	new.contentBelongUser = u
}
