/*
 * Basic Concepts
 * Glossary:
 * 		PL - Privacy Level
 *     WPL - Wall Privacy Level
 */
module basic

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

// Basic constraints
pred basicConstraints {
	// Each user owns one or more pieces of content
	all u : User | some c : Content | contentOwner[c] = u
	// Sysmetry friendship: all friends of mine should also treat me as friends
	all u : User | all f : u.friends | f -> u in friends
	// No self-friendship
	all u : User | u not in u.friends
	// A user can only tagged by his/own friends
	all u : User | all t : Tag | t.tagRefUser = u implies tagOwner[t] in u.friends
	// No cycle in comments chain
	all com : Comment | com not in com.^(commentBelongContent)
}

// Wall related constraints
pred wallConstraints {
	// A wall only belongs to one user
	all w : Wall | one userWall.w

	// All published content should only be published on exactly one wall
	all pub : Publishable | isContentOnWall[pub] implies one wallHasPub.pub
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

