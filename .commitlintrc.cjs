const copilotAutofixTitle = /^Potential fix for pull request finding(s)?$/i;

module.exports = {
  extends: ['@commitlint/config-conventional'],
  ignores: [
    (message) => copilotAutofixTitle.test(message.split('\n', 1)[0].trim()),
  ],
};
