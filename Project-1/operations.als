/*
 * Group 9
 * Project #1
 * Oct. 25th, 2019
 */

/*
 * Nicebook - Operations
 */

open privacy

// Base Event
abstract sig Event {
	n, n' : Nicebook
} {
	// Users never change, so do friendships
	n'.users = n.users
	n'.friendships = n.friendships
}

// Operations for publishables
abstract sig PublishableOp extends Event {
	pub : Publishable
} {
	// The tags should remain the same
	n'.pubTags = n.pubTags
}

// Operations for tags
abstract sig TagOp extends Event {
	tag : Tag
} {
	// The contents should remain the same
	n'.contents = n.contents
}

// Upload photo or note
sig UploadPub extends PublishableOp {
	// Which user owns the uploaded publishable
	u : User
} {
	// Pre Conditions
	u in n.users
	pub not in n.contents
	
	// Post Conditions
	n'.contents = n.contents + pub
	contentOwner[pub] = u
	!isContentOnWall[n', pub]
}

// Remove photo or note
sig RemovePub extends PublishableOp {
} {
	// Pre Conditions
	pub in n.contents

	// Post Conditions
	n'.contents = n.contents - (pub + ^commentBelongContent.pub)
}

// Publishing photo or note
sig PublishPub extends PublishableOp {
	// Which user's wall should this photo be published to
	u : User
} {
	// Pre Conditions
//	!isContentOnWall[n, pub]
	pub in n.contents
	contentOwner[pub] in (u + n.friendships[u])

	// Frame Conditions
	n'.contents = n.contents

	// Post condition
	isContentOnWall[n', pub] and userWall.(wallOfContent[n', pub]) = u
}

// Unpublish photo or note
sig UnpublishPub extends PublishableOp {
	u : User
} {
	// Pre Conditions
//	isContentOnWall[n, pub]
	pub in n.contents
	contentOwner[pub] = u or wallOfContent[n, pub] = u.userWall

	// Frame Conditions
	n'.contents = n.contents

	// Post Conditions
	!isContentOnWall[n', pub]
}

// Add Comment to a content
sig AddComment extends Event {
	// Comment to be added
	com : Comment,
	// Content attached to by the comment
	content : Content
} {
	// Frame Condition
	n'.pubTags = n.pubTags	

	// Pre Conditions
	//com not in n.contents
	content in n.contents
	// Pre - Privacy
	isContentOnWall[n, content]
	// Comply with privacy setting of the content owner
	let cOwner = contentOwner[com] |
		cOwner in contentViewer[n, content] and
			cOwner in getGroup[n, cOwner, cOwner.userContentCommentPL]

	// Post Conditions
	com.commentBelongContent = content
	n'.contents = n.contents + com
}

// Add tag to a content
sig AddTag extends TagOp {
	// We assume the performer of the operation is the owner of this publishable
	pub : Publishable
} {
	// Pre Conditions
	pub in n.contents
	//pub -> tag not in n.pubTags
	contentOwner[pub] in getGroup[n, tag.tagRefUser, Friends]

	// Post Conditions
	isContentOnWall[n', pub] and userWall.(wallOfContent[n', pub]) = tag.tagRefUser
	n'.pubTags = n.pubTags + pub -> tag
}

// Remove tag from a content
sig RemoveTag extends TagOp {
	// We assume the performer of the operation is the owner of this publishable
	pub: Publishable
} {
	// Pre Conditions
	//pub -> tag in n.pubTags
	pub in n.contents
	contentOwner[pub] in getGroup[n, tag.tagRefUser, Friends]

	// Post Conditions
	tag.tagRefUser.userWall not in wallOfContent[n', pub] 
	n'.pubTags = n.pubTags - pub -> tag
}

// Check the invariant preserves via by all of the operations(events)
assert NoPrivacyViolation {
	all pre, post : Nicebook, e : Event |
		invariant[pre] and e.n = pre and e.n' = post implies invariant[post]
}

//check NoPrivacyViolation

run {
	some pre, post : Nicebook, e : AddTag |
		invariant[pre] and e.n = pre and e.n' = post implies invariant[post]
}
