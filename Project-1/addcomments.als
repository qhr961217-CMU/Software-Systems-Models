/*
 * Nicebook - Operations
 */

open privacy

abstract sig Event {
	n, n' : Nicebook
}

// Upload, Remove, Publish and Unpublish
abstract sig ContentOp extends Event {
	content : Content
} {
	// Tags do not change
	n'.users <: tagRefUser = n.users <: tagRefUser
}
