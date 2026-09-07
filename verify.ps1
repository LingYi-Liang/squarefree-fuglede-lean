param([switch]$ReplayImports)

$ErrorActionPreference = 'Stop'
$auditPreviousLocation = Get-Location
$auditRoot = $PSScriptRoot
$auditLogRoot = Join-Path $auditRoot '.verification'

function Invoke-AuditCommand {
    param([string]$LogName, [string[]]$CommandArgs)
    & lake @CommandArgs 2>&1 | Tee-Object -FilePath (Join-Path $auditLogRoot $LogName)
    if ($LASTEXITCODE -ne 0) { throw "Failed: lake $($CommandArgs -join ' ')" }
}

try {
    Set-Location -LiteralPath $auditRoot
    New-Item -ItemType Directory -Path $auditLogRoot -Force | Out-Null
    @{ status = 'CHECKING'; entirePaperVerified = $false } |
        ConvertTo-Json | Set-Content -LiteralPath (Join-Path $auditLogRoot 'report.json') -Encoding utf8

    $auditRuntime = Get-Content -LiteralPath 'runtime-lock.json' -Raw | ConvertFrom-Json
    $auditLeanRevision = (& lean --githash).Trim()
    if ($LASTEXITCODE -ne 0 -or $auditLeanRevision -ne $auditRuntime.leanCommit) {
        throw 'Lean revision differs from runtime-lock.json.'
    }
    $auditSources = @(Get-ChildItem -LiteralPath 'FugledeAudit' -Filter '*.lean' | Sort-Object Name)
    $auditFiles = @($auditSources) + @(Get-Item -LiteralPath 'FugledeAudit.lean','StatementAudit.lean','AxiomAudit.lean','lean-toolchain','lakefile.toml','lake-manifest.json','runtime-lock.json')
    $auditHashes = @{}
    foreach ($auditFile in $auditFiles) {
        $auditHashes[$auditFile.FullName] = (Get-FileHash -LiteralPath $auditFile.FullName -Algorithm SHA256).Hash
    }
    if ($auditSources | Select-String -Pattern '\b(sorry|admit|axiom|native_decide|unsafe)\b') {
        throw 'Forbidden proof shortcut in authored proof sources.'
    }
    Invoke-AuditCommand -LogName 'build.log' -CommandArgs @('build')
    $auditMathlibRevision = (& git -C '.lake/packages/mathlib' rev-parse HEAD).Trim()
    if ($LASTEXITCODE -ne 0 -or $auditMathlibRevision -ne $auditRuntime.mathlibCommit) {
        throw 'Mathlib revision differs from runtime-lock.json.'
    }
    $auditChanges = @(& git -C '.lake/packages/mathlib' status --porcelain --untracked-files=no)
    if ($LASTEXITCODE -ne 0 -or $auditChanges.Count -ne 0) { throw 'Mathlib tracked files were modified.' }

    Invoke-AuditCommand -LogName 'statements.log' -CommandArgs @('env','lean','-DwarningAsError=true','StatementAudit.lean')
    foreach ($auditSource in $auditSources) {
        Write-Output "Rechecking $($auditSource.Name)"
        Invoke-AuditCommand -LogName ("source-" + $auditSource.BaseName + '.log') -CommandArgs @('env','lean','-DwarningAsError=true',('FugledeAudit/' + $auditSource.Name))
    }
    Invoke-AuditCommand -LogName 'axioms.log' -CommandArgs @('env','lean','AxiomAudit.lean')
    $auditNames = @($auditSources | Select-String -Pattern '^theorem\s+(\w+)' |
        ForEach-Object { 'FugledeAudit.' + $_.Matches[0].Groups[1].Value })
    $auditText = Get-Content -LiteralPath (Join-Path $auditLogRoot 'axioms.log') -Raw
    $auditRecords = @([regex]::Matches($auditText,
        "(?m)^'(?<name>[^']+)' (?:depends on axioms:\s*\[(?<deps>[^\]]*)\]|does not depend on any axioms)"))
    if ($auditRecords.Count -ne $auditNames.Count) { throw 'Incomplete theorem dependency audit.' }
    foreach ($auditName in $auditNames) {
        $auditRecord = @($auditRecords | Where-Object { $_.Groups['name'].Value -eq $auditName })
        if ($auditRecord.Count -ne 1) { throw "Missing or duplicated axiom report: $auditName" }
        foreach ($auditAxiom in ($auditRecord[0].Groups['deps'].Value -split ',')) {
            if ($auditAxiom.Trim() -notin @('propext','Classical.choice','Quot.sound','')) {
                throw "Unapproved dependency: $auditAxiom"
            }
        }
    }
    if ($ReplayImports) {
        Invoke-AuditCommand -LogName 'kernel-import-closure.log' -CommandArgs @('env','leanchecker','--fresh','--verbose','FugledeAudit')
    }
    foreach ($auditFile in $auditFiles) {
        if ((Get-FileHash -LiteralPath $auditFile.FullName -Algorithm SHA256).Hash -ne $auditHashes[$auditFile.FullName]) {
            throw "Input file changed during verification: $($auditFile.Name)"
        }
    }
    $auditResult = [ordered]@{
        checkedAt = (Get-Date).ToString('o')
        status = 'PASS_SELECTED_SCOPE'
        paperMainTheoremVerified = $true
        primeStepDescentVerified = $true
        unitInvarianceVerified = $true
        hadamardConsequenceVerified = $true
        entirePaperVerified = $false
        freshSourceChecks = 'PASS'
        statementChecks = 'PASS'
        axiomAllowlist = 'PASS'
        fullImportKernelReplay = [bool]$ReplayImports
        proofModuleCount = $auditSources.Count
        namedTheoremCount = $auditNames.Count
        leanCommit = $auditLeanRevision
        mathlibCommit = $auditMathlibRevision
        proofSourceHashes = @($auditSources | ForEach-Object {
            @{ file = $_.Name; sha256 = $auditHashes[$_.FullName] }
        })
    }
    $auditResult | ConvertTo-Json -Depth 6 |
        Set-Content -LiteralPath (Join-Path $auditLogRoot 'report.json') -Encoding utf8
    Write-Output 'PASS: selected formal statements. This is not a full-paper certification.'
}
catch {
    @{ checkedAt = (Get-Date).ToString('o'); status = 'FAILED'; entirePaperVerified = $false; failure = $_.Exception.Message } |
        ConvertTo-Json | Set-Content -LiteralPath (Join-Path $auditLogRoot 'report.json') -Encoding utf8
    throw
}
finally {
    Set-Location -LiteralPath $auditPreviousLocation.Path
}
