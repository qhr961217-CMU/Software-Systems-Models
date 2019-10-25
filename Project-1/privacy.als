/*
 * Group 9
 * Project #1
 * Oct. 25th, 2019
 */

/*
 * Nicebook - Privacy Control
 */
open basic

// Get the group that pl suggests with respect to the given user
fun getGroup[n : Nicebook, u : User, pl : PrivacyLevel] : set User {
	pl = OnlyMe
		=> u
	else pl = Friends
		=> u + n.friendships[u]
	else pl = FriendsOfFriends
		=> u + n.friendships[u] + n.friendships[n.friendships[u]]
	else
		User
}

// Get the set of all the viewers that can view the given content
fun contentViewer(n : Nicebook, c : Content) : set User {
	let owner = contentOwner[c], wall = wallOfContent[n, c] |
		// If the content is not published, it's only viewable to its owner
		no wall
			=> owner
		// The content is on the wall of its owner, where "contentViewWPL" controls visibility
		else	owner = userWall.wall
			=> getGroup[n, owner, c.contentViewWPL]
		// The content is on the wall of other users other than its owner,
		// where "friendContentViewWPL" setting of the wall owner controls visibility
		else
			getGroup[n, userWall.wall, userWall.wall.friendContentViewWPL]
}

// Returns the set of all content that can be viewed by the given user.
fun viewable[n : Nicebook, u : User] : set Content {
	{c : n.contents | u in contentViewer[n, c]}
}

// Returns whether p1's privacy level is lower than p2
pred isPLLowerOrEquals[p1 : PrivacyLevel, p2 : PrivacyLevel] {
	p1 = Everyone
		=> p2 in PrivacyLevel
	else p1 = FriendsOfFriends
		=> p2 in (PrivacyLevel - Everyone)
	else p1 = Friends
		=> p2 in (OnlyMe + Friends)
	else p1 = OnlyMe
		=> p2 = OnlyMe
}

// Privacy related constraints
pred privacyConstraints[n : Nicebook] {
	// The child comments privacy level should be lower or equal to the parent node privacy level.
	all c : commentsOfNicebook[n] | isPLLowerOrEquals[c.contentViewWPL, c.commentBelongContent.contentViewWPL]

	// Content must be published before it can be viewed by other users. (except user him/herself)
	all c : n.contents | !isContentOnWall[n, c] implies (contentViewer[n, c] = contentOwner[c])

	// A user may only comment contents that are viewable to him/her
	// Since the privacy setting is static:
 	// Every comment should be made by the user that can view the content that the comment is attatched to.
	// And it should comply with the comment's privacy level
	all com : commentsOfNicebook[n] |
		let comOwner = contentOwner[com],
			 attached = com.commentBelongContent,
			 attachedOwner = contentOwner[attached] | 
			comOwner in contentViewer[n, attached] and
			comOwner in getGroup[n, attachedOwner, attachedOwner.userContentCommentPL]
}

pred invariant[n : Nicebook] {
	basicConstraints[n]
	privacyConstraints[n]
}

generateValidPrivacyInstances : run {
	all n : Nicebook | invariant[n]
	some Nicebook
	some User
	some Publishable
	some Photo
	some Comment
	some Tag
} for 5
