// This tests partial initialization of structs
extern void echo(int x);

struct foo{
    int x;
    int y;
};

volatile struct foo pairOne = { .x = 1 };
volatile struct foo pairTwo = { .y = 2 };

int main(){
    echo(pairOne.x);
    echo(pairOne.y);
    echo(pairTwo.x);
    echo(pairTwo.y); 
    return 0;
}
