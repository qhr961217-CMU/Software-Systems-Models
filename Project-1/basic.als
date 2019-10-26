/*
 * Group 9
 * Project #1
 * Oct. 25th, 2019
 */

/*
 * Basic Concepts
 * Glossary:
 * 		PL - Privacy Level
 *     WPL - Wall Privacy Level
 */
module basic

sig Nicebook {
	users : set User,
	friendships : User -> User,
	contents: set Content,
	pubTags: Publishable lone -> Tag,
	wallPubs : Wall -> Publishable
} {
	// All users in friendship should be in users
	all u : friendships.User | u in users
	all u : User.friendships | u in users
	// All owners of the contents should be in users
	all c : contents | contentOwner[c] in users

	// All comments must belong to some content in this nicebook
	all com : (contents & Comment) | com.commentBelongContent in contents
	// All comments of all contents should be in this nicebook
	all con : contents | commentBelongContent.con in contents

	// All Publishable in pubTags should be in this Nicebook
	all pub : pubTags.Tag | pub in contents

	// Sysmetry friendship: all friends of mine should also treat me as friends
	all u1, u2 : users | u1 -> u2 in friendships implies u2 -> u1 in friendships
	// No self-friendship
	all u : users | u -> u not in friendships
}

sig User {
	userWall : one Wall,
	// Controls who can comment the user's contents
	userContentCommentPL : one PrivacyLevel,
	// Controls who can view the others' contents on the user's wall
	friendContentViewWPL : one PrivacyLevel
} {
	// All users should be in some nicebooks
	some users.this
}

abstract sig Content {
	// Who owns this content
	contentBelongUser : one User,
	// Controls who can view the content on the owner's wall
	contentViewWPL : one PrivacyLevel
} {
	// Every content has to be in some nicebooks
	some n : Nicebook | contentBelongUser in n.users and this in n.contents
}

abstract sig Publishable extends Content {
}

sig Note extends Publishable {
	noteHasPhoto : set Photo
}

sig Photo extends Publishable {} {
	// A photo is contained by at most one note
	lone noteHasPhoto.this
}

sig Comment extends Content {
	// What content is this comment attatched to
	commentBelongContent : one Content
}

sig Tag {
	// A tag reference one user
	tagRefUser : one User
}

sig Wall {} {
	// Every wall must belong to exactly one user
	one userWall.this
}

// Definitions of Privacy Levels
abstract sig PrivacyLevel {}
one sig OnlyMe extends PrivacyLevel {}
one sig Friends extends PrivacyLevel {}
one sig FriendsOfFriends extends PrivacyLevel {}
one sig Everyone extends PrivacyLevel {}


// Get the group that pl suggests with respect to the given user
fun getGroup[n : Nicebook, u : User, pl : PrivacyLevel] : set User {
	pl = OnlyMe
		=> u
	else pl = Friends
		=> u + n.friendships[u]
	else pl = FriendsOfFriends
		=> u + n.friendships[u] + n.friendships[n.friendships[u]]
	else
		n.users
}

// Get the owner of the content
fun contentOwner[c : Content] : one User {
	c.contentBelongUser
}

// Get the owner of the tag
fun tagOwner[n : Nicebook, t : Tag] : one User {
	n.pubTags.t.contentBelongUser
}

// Get the comments of Nicebook
fun commentsOfNicebook[n : Nicebook] : set Comment {
	commentBelongContent.(n.contents) & n.contents
}

// Get all the walls of the Nicebook
fun wallsOfNicebook[n : Nicebook] : set Wall {
	n.users.userWall
}

// Return true if the content is published on some wall
pred isContentOnWall[n : Nicebook, c : Content] {
		c in n.contents
       (c in Publishable) implies c in wallsOfNicebook[n].(n.wallPubs)
       // Comment is on wall iff its attatched content is on wall (recursively)
		(c in Comment) implies
               some pub : n.contents & Publishable | some w : wallsOfNicebook[n] |	
                       pub in w.(n.wallPubs) and pub in c.^commentBelongContent
}

// Get the wall of the content if there is any
fun wallOfContent[n : Nicebook, c : Content] : set Wall {
	c not in n.contents =>
		none
	else c in Publishable =>
		wallsOfNicebook[n] & n.wallPubs.c
	else
		// It's a comment, then return the wall that the highest parent of it is on
		{w : wallsOfNicebook[n] |
			some pub : Publishable |
				pub in w.(n.wallPubs) and pub in c.^commentBelongContent}
}

// Basic constraints
pred basicConstraints[n : Nicebook] {
	// A user can only tagged by his/own friends
	all u : n.users | all t : n.contents.(n.pubTags) | t.tagRefUser = u implies tagOwner[n, t] = u or (tagOwner[n, t] -> u in n.friendships)
	
	// No cycle in comments chain
	all com : commentsOfNicebook[n] | com not in com.^(commentBelongContent)

	// Publishable on walls must belong to its owner or the owner's firends
	all pub : wallsOfNicebook[n].(n.wallPubs) |
		all w : wallsOfNicebook[n] |
			pub in n.wallPubs[w] implies contentOwner[pub] in getGroup[n, userWall.w, Friends]
}

generateValidBasicInstances : run {
	all n : Nicebook | basicConstraints[n]
	some Nicebook
	some User
	some Publishable
	some Photo
	some Comment
	some Tag
} for 5

