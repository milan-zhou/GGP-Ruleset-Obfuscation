function obfuscate(rules, m) {
    let data = readdata(rules)
    let viz = new Set(["role", "base", "input", "init", "true", "does", "next", "legal", "goal", "terminal"])
    let constant = new Set(["rule", "not"])
    let tools = {
        "reverse": reverse,
        "expand" : expandProposition,
        "duplicate": duplicateProposition,
    }
    Object.keys(m).forEach( (k, i) => {
        if (m[k]["checked"]) {
            tools[k](data, viz, constant, 1 - m[k]["p"])
        }
    })
    return grindem(data).split("\r").join("\n")
}

function expandProposition(arr, viz, constant, p) {
    for (let i = 0; i < arr.length; i++) {
        if (arr[i][0] === "rule") {
            if (Math.random() > p ) {
                arr[i].push(arr[i][arr[i].length-1])
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

function reverse(arr, viz, constant, p) {
    let seen = new Set()
    let ignore = new Set()
    recReverse(arr, viz, constant, p, seen, ignore)    
}
function recReverse(arr, viz, constant, p, seen, ignore) {
    for (let i = 0; i < arr.length; i++) {
        if (typeof arr[i] === "object") {
            recReverse(arr[i], viz, constant, p, seen, ignore)
        } else {
            if (viz.has(arr[i]) || constant.has(arr[i]) || ignore.has(arr[i])) {
                continue
            }
            console.log(p)
            if (seen.has(arr[i])) {
                arr[i] = reverseString(arr[i])
            } else if (Math.random() > p) {
                seen.add(arr[i])
                arr[i] = reverseString(arr[i])
            } else {
                ignore.add(arr[i])
            }
        }
    }
}

function reverseString(str) {
    return str.split("").reverse().join("");
}

window.addEventListener("load", event => {
    let button = document.getElementById("obfuscate")
    button.addEventListener("click", event => {
        let input = document.getElementById("input")
        let flags = document.getElementsByName("flags")
        let probs = document.getElementsByName("probability")
        for (let i = 0; i < probs.length; i++) {
            if (probs[i].value < 0 || probs[i].value > 1) {
                return alert("Probabilities must be between 0 and 1")
            }
        }
        let m = new Object()
        for (let i = 0; i < flags.length; i++) {
            flag = flags[i]
            m[flag.value] = {
                "checked": flag.checked,
                "p": parseFloat(probs[i].value)
            }

        }
        console.log(m)
        let output = obfuscate(input.value, m)
        document.getElementById("output").value = output
    })
})