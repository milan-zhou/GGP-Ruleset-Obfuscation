function obfuscate(rules, m) {
    let data = readdata(rules)
    console.log(data)
    let viz = new Set(["role", "base", "input", "init", "true", "does", "next", "legal", "goal", "terminal"])
    let constant = new Set(["rule", "not"])
    let allEntities = collectEntities(data, viz, constant)
    let tools = {
        "replace": replace,
        "reverse": reverse,
        "expand" : expandProposition,
        "duplicate": duplicateProposition,
    }
    Object.keys(m).forEach( (k, i) => {
        if (m[k]["checked"]) {
            tools[k](data, viz, constant, 1 - m[k]["p"], allEntities)
        }
    })
    return grindem(data).split("\r").join("\n")
}

//May need early cutoff in goal propositions, no need to replace 100
function collectEntities(arr, viz, constant) {
    let allEntities = new Set([...viz, ...constant])
    recCollect(arr, allEntities)
    return allEntities
}

function recCollect(arr, allEntities) {
    for (let i = 0; i < arr.length; i++) {
        if (typeof arr[i] === "object") {
            recCollect(arr[i], allEntities)
        } else {
            allEntities.add(arr[i])
        }
    }
}

function replace(arr, viz, constant, p, allEntities) {
    let seen = new Object()
    let ignore = new Set()
    recReplace(arr, viz, constant, p, seen, ignore, allEntities) 
}

function recReplace(arr, viz, constant, p, seen, ignore, allEntities) {
    for (let i = 0; i < arr.length; i++) {
        if (typeof arr[i] === "object") {
            recReplace(arr[i], viz, constant, p, seen, ignore, allEntities)
        } else {
            if (viz.has(arr[i]) || constant.has(arr[i]) || ignore.has(arr[i])) {
                continue
            }
            if (arr[i] in seen) {
                arr[i] = seen[arr[i]]
            } else if (Math.random() > p) {
                let replacement = replaceEntity(seen, ignore, allEntities)
                seen[arr[i]] = replacement
                arr[i] = replacement
            } else {
                ignore.add(arr[i])
            }
        }
    }
}
function getRandomKey(obj) {
    var keys = Object.keys(obj)
    return keys[ keys.length * Math.random() << 0];
}

function replaceEntity(seen, ignore, allEntities) {
    let a = undefined
    let c= 0
    while (a == undefined) {
        if (c==10) {
            a = "RIP"
            break
        }
        let randomItem = getRandomKey(obfuscation_dictionary)
        if (!(randomItem in seen) && !ignore.has(randomItem) && !allEntities.has(randomItem)) {
            a = randomItem
        }
        c += 1
    }
    return a
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
