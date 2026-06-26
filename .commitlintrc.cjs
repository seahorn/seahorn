const copilotAutofixTitle = /^Potential fix for pull request finding(s)?$/i;
const copilotAutofixCoauthor =
  /^Co-authored-by:\s*Copilot Autofix powered by AI <\d+\+Copilot@users\.noreply\.github\.com>\s*$/im;

module.exports = {
  extends: ['@commitlint/config-conventional'],
  ignores: [
    (message) => {
      const trimmed = message.trim();
      const subject = trimmed.split('\n', 1)[0].trim();
      return (
        copilotAutofixTitle.test(subject) || copilotAutofixCoauthor.test(trimmed)
      );
    },
  ],
};
