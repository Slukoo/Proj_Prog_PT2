package main
import fmt

func plusone(x int) int{
	x++
	return x
}

func plusone2(p int*) int* {
	*p = *p + 1
	return p
}

func main() {
	var x int = 1
	var p int* = 10
	var x2 int = plusone(x)
	var p2 int* = plusone2(p)
	fmt.Print(x,p,x2,p2)
}
