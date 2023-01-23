package main
import "fmt"

func pointers() (int*,int*) {
	x1 := 123
	p1 := &x1
	p2 = new(int)
	p2* := 456
	return p1,p2
}


func main() {
	x,y := pointers
	a1,a2,a3,a4,a5,a6 := 9,9,9,9,9,9
	fmt.Print(*x,*y,a1,a2,a3,a4,a5,a6)
}