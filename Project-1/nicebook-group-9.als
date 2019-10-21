/*
 * Basic Concepts
 * Glossary:
 * 		PL - Privacy Level
 *     WPL - Wall Privacy Level
 */
sig User {
	friends : set User,
	userWall : one Wall,
	userContentCommentPL : one PrivacyLevel,
	friendContentViewWPL : one PrivacyLevel
}

abstract sig Content {
	contentBelongUser : one User,
	// A content only has PL iff it has been published
	contentViewWPL : lone PrivacyLevel
}

abstract sig Publishable extends Content {
	pubTag : set Tag
}

sig Note extends Publishable {
	noteHasPhoto : set Photo
}

sig Photo extends Publishable {}

sig Comment extends Content {
	commentBelongContent : one Content
}

sig Tag {
	// A tag reference one user
	tagRefUser : one User
} {
	// Every tag belongs to exactly one publishable
	one pubTag.this
}

sig Wall {
	wallHasPub : set Publishable
} {
	// Publishable on walls must belong to its owner or the owner's firends
	all pub : wallHasPub | contentOwner[pub] in (userWall.this +userWall.this.friends)
}

/*
 * Privacy Control
 */

abstract sig PrivacyLevel {}
one sig OnlyMe extends PrivacyLevel {}
one sig Friends extends PrivacyLevel {}
one sig FriendsOfFriends extends PrivacyLevel {}
one sig Everyone extends PrivacyLevel {}

// Get the owner of the content
fun contentOwner[c : Content] : one User {
	c.contentBelongUser
}

// Get the owner of the tag
fun tagOwner[t : Tag] : one User {
	pubTag.t.contentBelongUser
}

// Get the wall of the content if there is any
fun wallOfContent[c : Content] : one Wall {
	(c in Publishable) =>
		wallHasPub.c
	else
		{w : Wall |
			some pub : Publishable |
				pub in w.wallHasPub and pub in c.^commentBelongContent}
}

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

// Return true if the content is published on some wall
pred isContentOnWall[c : Content] {
	c in Publishable implies (some wallHasPub.c)
	// Comment is on wall iff its attatched content is on wall (recursively)
	c in Comment implies
		some pub : Publishable | some w : Wall |
			pub in w.wallHasPub and pub in c.^commentBelongContent
}

// Basic constraints
pred basicConstraints {
	// Sysmetry friendship: all friends of mine should also treat me as friends
	all u : User | all f : u.friends | f -> u in friends
	// No self-friendship
	all u : User | u not in u.friends
	// A user can only tagged by his/own friends
	all u : User | all t : Tag | t.tagRefUser = u implies tagOwner[t] in u.friends
}

// Wall related constraints
pred wallConstraints {
	// A wall only belongs to one user
	all w : Wall | one userWall.w

	// All published content should only be published on exactly one wall
	all pub : Publishable | isContentOnWall[pub] implies one wallHasPub.pub
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

run {
	invariant[]
} for 5
