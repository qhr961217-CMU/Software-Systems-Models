/*
 * Nicebook - Privacy Control
 */
open basic

// Get the group that pl suggests with respect to the given user
fun getGroup[u : User, pl : PrivacyLevel] : set User {
	pl = OnlyMe
		=> u
	else pl = Friends
		=> u + u.friends
	else pl = FriendsOfFriends
		=> u + u.friends + u.friends.friends
	else
		User
}

// Get the set of all the viewers that can view the given content
fun contentViewer(c : Content) : set User {
	let owner = contentOwner[c], wall = wallOfContent[c] |
		// If the content is not published, it's only viewable to its owner
		no wall
			=> owner
		// The content is on the wall of its owner, where "contentViewWPL" controls visibility
		else	owner = userWall.wall
			=> getGroup[owner, c.contentViewWPL]
		// The content is on the wall of other users other than its owner,
		// where "friendContentViewWPL" setting of the wall owner controls visibility
		else
			getGroup[userWall.wall, userWall.wall.friendContentViewWPL]
}


// Returns the set of all content that can be viewed by the given user.
fun viewable[u : User] : set Content {
	{c : Content | u in contentViewer[c]}
}


// Privacy related constraints
pred privacyConstraints {
	// All published content must have a PL
	all c : Content | isContentOnWall[c] implies (some c.contentViewWPL)

	// If a content is not published on wall, it doesn't have contentViewWPL
	// We assume "if a content doesn't have contentViewWPL, it means it's only viewable to its owner"
	// In other words, content must be published before it can be viewed by other users
	all c : Content | !isContentOnWall[c] implies (no c.contentViewWPL)

	// Content must be published before it can be viewed by other users. (except user him/herself)
	all c : Content | !isContentOnWall[c] implies (contentViewer[c] = contentOwner[c])

	// A user may only comment contents that are viewable to him/her
	// Since the privacy setting is static:
 	// Every comment should be made by the user that can view the content that the comment is attatched to.
	// And it should comply with the comment
	all com : Comment |
		let comOwner = contentOwner[com],
			 attached = com.commentBelongContent,
			 attachedOwner = contentOwner[attached] | 
			comOwner in contentViewer[attached] and
			comOwner in getGroup[attachedOwner, attachedOwner.userContentCommentPL]
}

// Assumptions we made to resolve the ambiguities
pred assumptions {
	// Sysmetry friendship: all friends of mine should also treat me as friends
	// If a content is not published on wall, it doesn't have contentViewWPL
	// All published content should only be published on exactly one wall
	// Privacy setting is static
}

pred invariant[] {
	basicConstraints
	wallConstraints
	privacyConstraints
}

assert NoPrivacyVialation {
	all u : User |
		all com : contentBelongUser.u & Comment | com.commentBelongContent in viewable[u]

	// TODO: How to check whether a user has access to a content she/he can view but not comment
}

//run {
//	invariant[]
//}

check NoPrivacyVialation
