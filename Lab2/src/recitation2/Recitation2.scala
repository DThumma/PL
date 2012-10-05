package recitation2

object Recitation2 {
	sealed abstract class LinkedList
	case object Empty extends LinkedList
	case class Node(value: Int, next: LinkedList) extends LinkedList
	
	def insertAtEnd(list: LinkedList, number: Int): LinkedList = {
	  return list
	}
}