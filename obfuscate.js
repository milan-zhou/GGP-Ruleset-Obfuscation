function obfuscate() {
    let rules = 
    `role(white)
    role(black)
  
    base(p)
    base(q)
    base(r)
    base(s)
  
    action(a)
    action(b)
    action(c)
    action(d)
  
    init(s)
  
    legal(white,a)
    legal(white,b)
    legal(white,c)
    legal(black,d)
    
    next(p) :- does(white,a) & ~true(p)
    next(p) :- ~does(white,a) & true(p)
    next(q) :- does(white,b) & true(p)
    next(q) :- does(white,c) & true(r)
    next(q) :- ~does(white,b) & ~does(white,c) & true(q)
    next(r) :- does(white,c) & true(q)
    next(r) :- ~does(white,c) & true(r)

    goal(white,100) :- terminal
    goal(white,0) :- ~terminal
    goal(black,100) :- terminal
    goal(black,0) :- ~terminal

    terminal :- true(p) & true(q) & true(r)
    `
    let data = readdata(rules)
    let viz = new Set(["role", "base", "input", "init", "true", "does", "next", "legal", "goal", "terminal"])
    let constant = new Set(["rule", "not"])
    console.log(data)
    // recReverse(data, viz, constant)
    // duplicateProposition(data, viz, constant, .5)
    expandProposition(data, viz, constant, .5)
    // let request = new XMLHttpRequest()
    // request.open("GET","https://cors.io/?http://randomword.setgetgo.com/get.php")
    // request.responseType = "jsonp"
    // request.onload = function() {
    //     console.log(request.responseText)
    // };
    // request.send();
    console.log(grindem(data).split("\r").join("\n"))
}

function expandProposition(arr, viz, constant, p) {
    for (let i = 0; i < arr.length; i++) {
        if (arr[i][0] === "rule") {
            if (Math.random() > p ) {
                arr[i].push(arr[i][arr[i].length-1])
                console.log(arr[i])
            }
        }
    }
}

function duplicateProposition(arr, viz, constant, p) {
    for (let i = 0; i < arr.length; i++) {
        if (viz.has(arr[i][0] || constant.has(arr[i][0]))) {
            continue
        }
        if (Math.random() > p) {
            arr.splice(i, 0,arr[i])
            i++ 
        }
        
    }
}

function recReverse(arr, viz, constant) {
    for (let i = 0; i < arr.length; i++) {
        if (typeof arr[i] === "object") {
            recReverse(arr[i], viz, constant)
        } else {
            if (viz.has(arr[i]) || constant.has(arr[i])) {
                continue
            }
            arr[i] = reverseString(arr[i])
        }
    }
}

function reverseString(str) {
    return str.split("").reverse().join("");
}