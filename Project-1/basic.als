/*
 * Basic Concepts
 * Glossary:
 * 		PL - Privacy Level
 *     WPL - Wall Privacy Level
 */
module basic

sig Nicebook {
	users : set User
}

sig User {
	friends : set User,
	userWall : one Wall,
	userContentCommentPL : one PrivacyLevel,
	friendContentViewWPL : one PrivacyLevel
} {
	some users.this
}

abstract sig Content {
	contentBelongUser : one User,
	// Controls who can view the content on the owner's wall
	contentViewWPL : one PrivacyLevel
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
	// Publishable on walls must belong to its owner or the owner's firends
	all pub : wallHasPub | contentOwner[pub] in (userWall.this +userWall.this.friends)
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

// Return true if the content is published on some wall
pred isContentOnWall[c : Content] {
       c in Publishable implies (some wallHasPub.c)
       // Comment is on wall iff its attatched content is on wall (recursively)
       c in Comment implies
               some pub : Publishable | some w : Wall |
                       pub in w.wallHasPub and pub in c.^commentBelongContent
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

fun contentsOfNicebook[n : Nicebook] : set Content {
	contentBelongUser.(n.users)
}

fun commentsOfNicebook[n : Nicebook] : set Comment {
	commentBelongContent.(contentsOfNicebook[n])
}

// Basic constraints
pred basicConstraints[n : Nicebook] {
	// Each user owns one or more pieces of content
	all u : n.users | some c : Content | contentOwner[c] = u
	// Sysmetry friendship: all friends of mine should also treat me as friends
	all u : n.users | all f : u.friends | f -> u in friends
	// No self-friendship
	all u : n.users | u not in u.friends
	// A user can only tagged by his/own friends
	all u : n.users | all t : Tag | t.tagRefUser = u implies tagOwner[t] in u.friends
	
	// No cycle in comments chain
	all com : commentsOfNicebook[n] | com not in com.^(commentBelongContent)
}

// local operation for addTag
pred addTagToPublishable[p, p' : Publishable, t : Tag]{
	// user of the tag u = t.tagRefUser
	// p'.pubTag = p.pubTag + t 
	// u.userWall.wallHasPub contains pubTag.t
	
	// postcondition
	some u : t.tagRefUser | 
	p'.pubTag = p.pubTag + t and pubTag.t in u.userWall.wallHasPub

	// frame condition
	all t : p.pubTag | 
	t in p'.pubTag
}

// local operation for removeTag
pred removeTagFromPublishable[p, p' : Publishable, t : Tag]{
	// precondition
	t in p.pubTag
		
	// postcondition
	t not in p'.pubTag
	
	// frame condition
	all tag : p.pubTag - t | 
	tag in p'.pubTag
}

pred addTag{
}

pred removeTag{
}

