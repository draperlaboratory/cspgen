// This tests structs with initializers
extern void echo(int x);

struct foo{
    int x;
    int y;
};

volatile struct foo pair = { .x = 1, .y=2 };

int main(){
    echo(pair.x);
    echo(pair.y);
    return 0;
}
