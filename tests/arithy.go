package main
import "fmt"

func f() (string, string){
	return "Hello ", "stranger"
}

func g(a string, b string) (string, string, string, string){
	return a, b, ", how are you", "today?\n"
}

func a2(x int) (int,int) {
	return x,x*x
}

func a3(x int, y int) (int,int,int) {
	return x,y,x*y
}

func a4(x,y,z int) (int,int,int,int) {
	return x, x+y, z, x+z+y
}

func main() {
	fmt.Print(g(f()))
	a,b,c,d := a4(a3(a2(2)))
	fmt.Print(a,b,c,d)
}