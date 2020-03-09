sig Book {}
sig User {borrowed: set Book}
sig SeniorUser extends User {}

--Question 1
pred BorrowRules { 
	--each book borrowed by <= 1 User
	all b: Book | # b.(~borrowed) =1 or # b.(~borrowed) = 0
	--SeniorUser can borrow any no. of books	
	all u: User - SeniorUser | # u.borrowed = 1 or # u.borrowed = 0 
}

pred Show {}

--Question 2.1
pred borrow[u: User, b: Book, borrowed1: User -> set Book] {
	--check for book availability
	(#b.(~borrowed)=0 and (u not in SeniorUser and #u.borrowed=0) or u in SeniorUser)
	--adding (User, Book) in the borrowed relation
	implies borrowed + u->b=borrowed1
	--no book is borrowed
	else borrowed=borrowed1
}
	
 --Question2.2
pred return[u: User,	b: Book, borrowed1: User -> set Book] {
	--return book
	b in u.borrowed
 	--remove (User, Book) from the borrowed relation
	implies borrowed - (u->b) = borrowed1
	--no book is borrowed
	else borrowed = borrowed1
}

pred verifyBorrow[u: User, b: Book, borrowed1: User -> set Book] {
	--wrapper pred for borrow
	borrow[u, b, borrowed]
	not BorrowRules[]
}

pred verifyReturn[u: User,	b: Book, borrowed1: User -> set Book]{
	--wrapper pred for return
	return[u, b, borrowed]
	not BorrowRules[]
}

fact BorrowRules {BorrowRules}

run Show for 7

run BorrowRules for 7

run borrow for 8

run return for 9

run verifyBorrow for 9

run verifyReturn for 9
