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
	contents: set Content
} {
	// All users in friendship should be in users
	all u : friendships.User | u in users
	all u : User.friendships | u in users
	// All owners of the contents should be in users
	all c : contents | contentOwner[c] in users
}

sig User {
	userWall : one Wall,
	userContentCommentPL : one PrivacyLevel,
	friendContentViewWPL : one PrivacyLevel
} {
	// All users should be in some nicebooks
	some users.this
}

abstract sig Content {
	contentBelongUser : one User,
	// Controls who can view the content on the owner's wall
	contentViewWPL : one PrivacyLevel
} {
	some n : Nicebook | contentBelongUser in n.users and this in n.contents
}

abstract sig Publishable extends Content {
	pubTag : set Tag
}

sig Note extends Publishable {
	noteHasPhoto : set Photo
}

sig Photo extends Publishable {} {
	// A photo is contained by at most one note
	lone noteHasPhoto.this
}

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
	// Every wall must belong to exactly one user
	one userWall.this
}

// Definitions of Privacy Levels
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

fun commentsOfNicebook[n : Nicebook] : set Comment {
	commentBelongContent.(n.contents)
}

fun wallsOfNicebook[n : Nicebook] : set Wall {
	n.users.userWall
}

// Return true if the content is published on some wall
pred isContentOnWall[n : Nicebook, c : Content] {
       (c in Publishable) implies (c in n.contents and c in wallsOfNicebook[n].wallHasPub)
       // Comment is on wall iff its attatched content is on wall (recursively)
       (c in Comment) implies c in n.contents and
               some pub : n.contents & Publishable | some w : wallsOfNicebook[n] |
                       pub in w.wallHasPub and pub in c.^commentBelongContent
}

// Get the wall of the content if there is any
fun wallOfContent[n : Nicebook, c : Content] : one Wall {
	c not in n.contents =>
		none
	else c in Publishable =>
		wallsOfNicebook[n] & wallHasPub.c
	else
		// It's a comment
		{w : wallsOfNicebook[n] |
			some pub : Publishable |
				pub in w.wallHasPub and pub in c.^commentBelongContent}
}

// Basic constraints
pred basicConstraints[n : Nicebook] {
	// Each user owns one or more pieces of content
	all u : n.users | some c : Content | contentOwner[c] = u
	// Sysmetry friendship: all friends of mine should also treat me as friends
	all u1, u2 : n.users | u1 -> u2 in n.friendships implies u2 -> u1 in n.friendships
	// No self-friendship
	all u : n.users | u -> u not in n.friendships
	// A user can only tagged by his/own friends
	all u : n.users | all t : Tag | t.tagRefUser = u implies (tagOwner[t] -> u in n.friendships)
	
	// No cycle in comments chain
	all com : commentsOfNicebook[n] | com not in com.^(commentBelongContent)

	// Publishable on walls must belong to its owner or the owner's firends
	all pub : n.users.userWall.wallHasPub |
		let wallOwner = userWall.(wallOfContent[n, pub]) |
		isContentOnWall[n, pub] implies
			contentOwner[pub] in (wallOwner + n.friendships[wallOwner])
}

run {
	all n : Nicebook | basicConstraints[n]
} for 2 but exactly 2 Nicebook

