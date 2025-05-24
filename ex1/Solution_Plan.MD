So what do we need to do?

From Lecture:
1. Assign type variables
2. Generate type constrains
3. solve constraints 

always have the types of primitives.

when trying to infer the type of a Lambda
    1. have the argument:
        a. 1 argument 
        b. couple of arguments - syntactic sugar for nested functions
            -> need to translate to funcs fo 1 argument each
    2. the body -> defines the return (ret) type
        what can we have in the body?
            another lambda, application, free var, let, 

    how is the type of an application deducted?
        application is of the form: u v
        => u(v)
        then the argument type of u is the typeof( v ) 
        =>  u: typeof(v) -> typeof(?) will need ot find out what is u by finding out what is above u in the tree. 

stopping update of types in the first var that we saw. (overshadowing)

1. building the tree — assign types (abstractly) to everything
2. 



        

        


