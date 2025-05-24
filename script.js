// SAT Solver использующий алгоритм DPLL (Davis-Putnam-Logemann-Loveland)

/**
 * Класс для работы с формулами в КНФ (конъюнктивной нормальной форме)
 * КНФ представляет собой конъюнкцию (И) дизъюнкций (ИЛИ) литералов
 * Литерал - это переменная или ее отрицание
 */
class SATSolver {
    /**
     * Конструктор класса SATSolver
     */
    constructor() {
        this.steps = []; // Хранит шаги решения для визуализации
    }

    /**
     * Основная функция решения SAT с помощью алгоритма DPLL
     * @param {Array} formula - Формула в КНФ. Представлена как массив дизъюнктов (предложений)
     * @param {Object} assignment - Текущее присваивание переменных
     * @returns {Object|null} - Возвращает присваивание, удовлетворяющее формуле, или null, если решения нет
     */
    solve(formula, assignment = {}) {
        this.steps = [];
        return this.dpll(formula, assignment);
    }

    /**
     * Рекурсивная реализация алгоритма DPLL
     * @param {Array} formula - Формула в КНФ
     * @param {Object} assignment - Текущее присваивание переменных
     * @returns {Object|null} - Возвращает присваивание, удовлетворяющее формуле, или null, если решения нет
     */
    dpll(formula, assignment) {
        // Добавляем шаг для визуализации
        this.steps.push({
            formula: JSON.parse(JSON.stringify(formula)),
            assignment: JSON.parse(JSON.stringify(assignment)),
            type: 'check'
        });

        // Если формула пуста, значит все предложения удовлетворены
        if (formula.length === 0) {
            return assignment;
        }

        // Если есть пустое предложение, формула не выполнима с текущим присваиванием
        if (formula.some(clause => clause.length === 0)) {
            this.steps.push({
                formula,
                assignment,
                type: 'backtrack',
                reason: 'Найдено пустое предложение'
            });
            return null;
        }

        // Упрощение формулы с помощью правила единичного литерала
        const unitPropResult = this.unitPropagation(formula, assignment);
        formula = unitPropResult.formula;
        assignment = unitPropResult.assignment;

        // Если после упрощения найдено противоречие
        if (formula === null) {
            return null;
        }

        // Упрощение с помощью правила чистого литерала
        const pureLiteralResult = this.pureLiteralElimination(formula, assignment);
        formula = pureLiteralResult.formula;
        assignment = pureLiteralResult.assignment;

        // Выбираем переменную для ветвления
        const variable = this.selectVariable(formula);
        if (!variable) {
            // Если больше нет переменных, но формула не пуста,
            // то формула не выполнима
            if (formula.length > 0) {
                return null;
            }
            return assignment;
        }

        // Пробуем присвоить переменной значение true
        this.steps.push({
            formula,
            assignment,
            type: 'branch',
            variable,
            value: true
        });

        const assignmentTrue = {
            ...assignment,
            [variable]: true
        };
        const resultTrue = this.dpll(this.substitute(formula, variable, true), assignmentTrue);

        if (resultTrue !== null) {
            return resultTrue;
        }

        // Если не получилось, пробуем присвоить false
        this.steps.push({
            formula,
            assignment,
            type: 'branch',
            variable,
            value: false
        });

        const assignmentFalse = {
            ...assignment,
            [variable]: false
        };
        return this.dpll(this.substitute(formula, variable, false), assignmentFalse);
    }

    /**
     * Упрощение формулы с помощью правила единичного литерала
     * Если в предложении есть только один литерал, мы должны присвоить ему значение,
     * которое сделает предложение истинным
     * @param {Array} formula - Формула в КНФ
     * @param {Object} assignment - Текущее присваивание переменных
     * @returns {Object} - Упрощенная формула и обновленное присваивание
     */
    unitPropagation(formula, assignment) {
        let result = {
            formula: [...formula],
            assignment: {
                ...assignment
            }
        };

        let foundUnit = true;
        while (foundUnit) {
            foundUnit = false;

            for (let i = 0; i < result.formula.length; i++) {
                const clause = result.formula[i];

                if (clause.length === 1) {
                    foundUnit = true;
                    const literal = clause[0];
                    const variable = literal.startsWith('!') ? literal.substring(1) : literal;
                    const value = !literal.startsWith('!');

                    this.steps.push({
                        formula: result.formula,
                        assignment: result.assignment,
                        type: 'unit',
                        variable,
                        value
                    });

                    result.assignment[variable] = value;
                    result.formula = this.substitute(result.formula, variable, value);

                    // Проверяем, не привело ли это к противоречию
                    if (result.formula.some(c => c.length === 0)) {
                        this.steps.push({
                            formula: result.formula,
                            assignment: result.assignment,
                            type: 'conflict',
                            reason: 'Противоречие после правила единичного литерала'
                        });
                        return {
                            formula: null,
                            assignment: result.assignment
                        };
                    }

                    break; // Начинаем поиск сначала, так как формула изменилась
                }
            }
        }

        return result;
    }

    /**
     * Упрощение формулы с помощью правила чистого литерала
     * Если литерал появляется только в одной полярности (положительной или отрицательной),
     * мы можем присвоить ему значение, которое сделает все предложения с ним истинными
     * @param {Array} formula - Формула в КНФ
     * @param {Object} assignment - Текущее присваивание переменных
     * @returns {Object} - Упрощенная формула и обновленное присваивание
     */
    pureLiteralElimination(formula, assignment) {
        let changed = true;
        let result = {
            formula: [...formula],
            assignment: {
                ...assignment
            }
        };

        while (changed) {
            changed = false;
            // собираем текущие множества литералов
            const countPos = {},
                countNeg = {};
            for (const clause of result.formula) {
                for (const lit of clause) {
                    const varName = lit.startsWith('!') ? lit.slice(1) : lit;
                    if (lit.startsWith('!')) countNeg[varName] = (countNeg[varName] || 0) + 1;
                    else countPos[varName] = (countPos[varName] || 0) + 1;
                }
            }

            // ищем чистые литералы
            for (const variable of Object.keys({
                    ...countPos,
                    ...countNeg
                })) {
                if (result.assignment.hasOwnProperty(variable)) continue;
                const hasPos = !!countPos[variable],
                    hasNeg = !!countNeg[variable];
                if (hasPos ^ hasNeg) {
                    const value = hasPos;
                    // помним шаг для визуализации (клонируем формулу и присваивание)
                    this.steps.push({
                        type: 'pure',
                        variable,
                        value,
                        formula: JSON.parse(JSON.stringify(result.formula)),
                        assignment: {
                            ...result.assignment
                        }
                    });
                    // фиксируем присваивание
                    result.assignment[variable] = value;
                    // подстановка — можно использовать уже исправленный substitute
                    result.formula = this.substitute(result.formula, variable, value);
                    changed = true;
                    break; // пересобираем счётчики заново
                }
            }
        }

        return result;
    }

    /**
     * Выбор переменной для ветвления
     * Здесь можно реализовать различные эвристики выбора переменной
     * @param {Array} formula - Формула в КНФ
     * @returns {string|null} - Выбранная переменная или null, если нет переменных
     */
    selectVariable(formula) {
        // считаем частоту появлений каждого литерала
        const freq = {};
        for (const clause of formula) {
            for (const lit of clause) {
                const varName = lit.startsWith('!') ? lit.slice(1) : lit;
                freq[varName] = (freq[varName] || 0) + 1;
            }
        }
        // выбираем переменную с наибольшей частотой
        let bestVar = null,
            bestCount = -1;
        for (const [variable, count] of Object.entries(freq)) {
            if (!bestVar || count > bestCount) {
                bestVar = variable;
                bestCount = count;
            }
        }
        return bestVar;
    }


    /**
     * Замена переменной в формуле на заданное значение
     * @param {Array} formula - Формула в КНФ
     * @param {string} variable - Переменная для замены
     * @param {boolean} value - Значение переменной
     * @returns {Array} - Упрощенная формула после подстановки
     */
    substitute(formula, variable, value) {
        const result = [];
        for (const clause of formula) {
            let satisfied = false;
            const newClause = [];
            for (const literal of clause) {
                const litVar = literal.startsWith('!') ? literal.slice(1) : literal;
                const isNeg = literal.startsWith('!');
                if (litVar === variable) {
                    const litVal = isNeg ? !value : value;
                    if (litVal) {
                        satisfied = true;
                        break; // удаляем всю клаузу
                    } else {
                        continue; // просто убираем ложный литерал
                    }
                }
                newClause.push(literal);
            }
            if (!satisfied) {
                result.push(newClause);
            }
        }
        return result;
    }


    /**
     * Парсер строки с формулой в КНФ
     * Поддерживает форматы:
     * - (a | b | !c) & (!a | d) & (c | !d | e)
     * - [[a, b, !c], [!a, d], [c, !d, e]]
     * @param {string} input - Строка с формулой
     * @returns {Array} - Формула в КНФ (массив массивов литералов)
     */
    parseFormula(input) {
        let formula;

        try {
            // Сначала пробуем распарсить как JSON
            formula = JSON.parse(input);

            // Проверяем, что это массив массивов строк
            if (!Array.isArray(formula) || !formula.every(clause =>
                    Array.isArray(clause) && clause.every(lit => typeof lit === 'string'))) {
                throw new Error("Неверный формат JSON");
            }
        } catch (e) {
            // Если не получилось как JSON, парсим как текстовую формулу
            formula = input.split('&').map(clause => {
                return clause.replace(/[()]/g, '').trim().split('|').map(lit => lit.trim());
            });
        }

        return formula;
    }

    /**
     * Получить шаги решения для визуализации
     * @returns {Array} - Массив шагов решения
     */
    getSteps() {
        return this.steps;
    }

    /**
     * Преобразование формулы в строковое представление
     * @param {Array} formula - Формула в КНФ
     * @returns {string} - Строковое представление формулы
     */
    formulaToString(formula) {
        return formula.map(clause =>
            '(' + clause.join(' | ') + ')'
        ).join(' & ');
    }
}

// Функция для проверки выполнимости формулы с данным присваиванием
function checkSatisfiability(formula, assignment) {
    for (const clause of formula) {
        let clauseSatisfied = false;

        for (const literal of clause) {
            const variable = literal.startsWith('!') ? literal.substring(1) : literal;
            const isNegated = literal.startsWith('!');
            const variableValue = assignment[variable] !== undefined ? assignment[variable] : null;

            if (variableValue === null) {
                // Если переменной нет в присваивании, считаем что она не делает предложение истинным
                continue;
            }

            // Литерал истинен, если он не отрицание и переменная истинна
            // или если он отрицание и переменная ложна
            const literalValue = isNegated ? !variableValue : variableValue;

            if (literalValue) {
                clauseSatisfied = true;
                break;
            }
        }

        if (!clauseSatisfied) {
            return false;
        }
    }

    return true;
}

// Обработчики UI для тестирования
document.addEventListener('DOMContentLoaded', function () {
    const formulaInput = document.getElementById('formula');
    const solveButton = document.getElementById('solve');
    const resultsContainer = document.getElementById('results-container');
    const solutionResult = document.getElementById('solution-result');
    const verificationResult = document.getElementById('verification-result');
    const stepsContainer = document.getElementById('steps-container');
    const assignmentContainer = document.getElementById('assignment-container');
    const examples = document.querySelectorAll('.example');

    // Обработчик для примеров формул
    examples.forEach(example => {
        example.addEventListener('click', function () {
            formulaInput.value = this.getAttribute('data-formula');
        });
    });

    // Обработчик кнопки решения
    solveButton.addEventListener('click', function () {
        // Очищаем предыдущие результаты
        stepsContainer.innerHTML = '';
        assignmentContainer.innerHTML = '';

        // Получаем формулу из поля ввода
        const formulaText = formulaInput.value.trim();
        if (!formulaText) {
            alert('Пожалуйста, введите булеву формулу');
            return;
        }

        try {
            // Создаем решатель
            const solver = new SATSolver();

            // Парсим формулу
            const formula = solver.parseFormula(formulaText);

            // Выводим исходную формулу
            solutionResult.innerHTML = `<p><strong>Исходная формула:</strong> ${solver.formulaToString(formula)}</p>`;

            // Решаем SAT
            console.time('Solving time');
            const solution = solver.solve(formula);
            if (solution && checkSatisfiability(formula, solution)) {
                console.log("OK");
            } else {
                console.error("Найдено некорректное решение!");
            }


            // Выводим результат
            if (solution !== null) {
                solutionResult.innerHTML += `<p><strong>Решение найдено!</strong></p>`;

                // Проверяем решение
                const isSatisfiable = checkSatisfiability(formula, solution);
                verificationResult.innerHTML = `<p><strong>Проверка:</strong> ${isSatisfiable ? 'Решение верно' : 'Ошибка! Решение не удовлетворяет формуле'}</p>`;

                // Выводим присваивание переменных
                const assignmentTable = document.createElement('table');
                assignmentTable.innerHTML = `
                            <tr>
                                <th>Переменная</th>
                                <th>Значение</th>
                            </tr>
                        `;


                Object.keys(solution) // Получаем массив переменных
                    .sort() // Сортируем по алфавиту
                    .forEach(variable => { // Перебираем отсортированный массив
                        const row = document.createElement('tr');
                        row.innerHTML = `
                                <td>${variable}</td>
                                <td>${solution[variable] ? 'true' : 'false'}</td>
                            `;
                        assignmentTable.appendChild(row);
                    })

                assignmentContainer.appendChild(assignmentTable);
            } else {
                solutionResult.innerHTML += `<p><strong>Формула невыполнима!</strong></p>`;
                verificationResult.innerHTML = '';
            }

            // Выводим шаги решения
            const steps = solver.getSteps();

            steps.forEach((step, index) => {
                const stepDiv = document.createElement('div');
                stepDiv.className = `step ${step.type}`;

                let stepHTML = `<p><strong>Шаг ${index + 1}:</strong> `;

                switch (step.type) {
                    case 'check':
                        stepHTML += `Проверка формулы</p>`;
                        break;
                    case 'unit':
                        stepHTML += `Единичный литерал: ${step.variable} = ${step.value ? 'true' : 'false'}</p>`;
                        break;
                    case 'pure':
                        stepHTML += `Чистый литерал: ${step.variable} = ${step.value ? 'true' : 'false'}</p>`;
                        break;
                    case 'branch':
                        stepHTML += `Ветвление: ${step.variable} = ${step.value ? 'true' : 'false'}</p>`;
                        break;
                    case 'backtrack':
                        stepHTML += `Откат (${step.reason || 'невыполнимая ветвь'})</p>`;
                        break;
                    case 'conflict':
                        stepHTML += `Конфликт: ${step.reason || 'противоречие'}</p>`;
                        break;
                }

                // Добавляем текущую формулу
                if (step.formula) {
                    stepHTML += `<p>Формула: ${solver.formulaToString(step.formula)}</p>`;
                }

                // Добавляем текущее присваивание
                if (step.assignment && Object.keys(step.assignment).length > 0) {
                    stepHTML += `<p>Присваивание: {`;
                    stepHTML += Object.entries(step.assignment)
                        .map(([key, value]) => `${key}: ${value ? 'true' : 'false'}`)
                        .join(', ');
                    stepHTML += `}</p>`;
                }

                stepDiv.innerHTML = stepHTML;
                stepsContainer.appendChild(stepDiv);
            });

            // Показываем результаты
            resultsContainer.style.display = 'block';

        } catch (error) {
            alert(`Ошибка: ${error.message}`);
            console.error(error);
        }
    });
});