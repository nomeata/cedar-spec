permit(
  principal,
  action,
  resource == a::"h"
) when {
  (true && (if context then principal else principal)) && principal
};
